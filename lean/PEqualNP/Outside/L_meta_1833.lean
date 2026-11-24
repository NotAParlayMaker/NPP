import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1833

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun acc g => acc ++ [f g acc]) init

theorem run_snoc {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α) :
    run f (gs ++ [g]) init = run f gs init ++ [f g (run f gs init)] := by
  simp [run, List.foldl_append]

theorem run_app {α : Type} (f : Gate → List α → α) (as bs : List Gate) (init : List α) :
    run f (as ++ bs) init = run f bs (run f as init) := by
  simp [run, List.foldl_append]

theorem run_len {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) :
    (run f gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_pre {α : Type} (f : Gate → List α → α) (bs : List Gate) (init : List α) :
    ∃ t, run f bs init = init ++ t := by
  induction bs using List.reverseRecOn with
  | nil => exact ⟨[], by simp [run]⟩
  | append_singleton bs g ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [f g (run f bs init)], ?_⟩
    rw [run_snoc, ← List.append_assoc, ← ht]

theorem run_stab {α : Type} (f : Gate → List α → α) (pre suf : List Gate) (init : List α) (d : α)
    (i : ℕ) (hi : i < init.length + pre.length) :
    (run f (pre ++ suf) init).getD i d = (run f pre init).getD i d := by
  rw [run_app]
  obtain ⟨t, ht⟩ := run_pre f suf (run f pre init)
  rw [ht, List.getD_append _ _ _ _ (by rw [run_len]; exact hi)]

theorem stab2 {α : Type} (f : Gate → List α → α) (gs pre : List Gate) (g : Gate) (suf : List Gate)
    (h : gs = pre ++ g :: suf) (init : List α) (d : α) (i : ℕ)
    (hi : i < init.length + pre.length) :
    (run f gs init).getD i d = (run f pre init).getD i d := by
  subst h
  exact run_stab f pre (g :: suf) init d i hi

theorem run_last {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α)
    (d : α) : (run f (gs ++ [g]) init).getD (init.length + gs.length) d = f g (run f gs init) := by
  rw [run_snoc, List.getD_append_right _ _ _ _ (by rw [run_len]), run_len, Nat.sub_self,
    List.getD_cons_zero]

def evf (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def dgf (g : Gate) (d : List ℕ) : ℕ := g.lineDegree d

def ini (n : ℕ) (M : Finset ℕ) : List ℕ := (List.range n).map fun i => if i ∈ M then 1 else 0

theorem ini_len (n : ℕ) (M : Finset ℕ) : (ini n M).length = n := by simp [ini]

theorem ini_getD (n : ℕ) (M : Finset ℕ) (w : ℕ) (hw : w < n) (hM : w ∉ M) :
    (ini n M).getD w 0 = 0 := by
  unfold ini
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp [hM]

theorem ev_and (g : Gate) (w : List Bool) (a b : ℕ) (ho : g.op = GateOp.and)
    (hi : g.inputs = [a, b]) : evf g w = (w.getD a false && w.getD b false) := by
  unfold evf; rw [ho, hi]; simp [GateOp.eval]

theorem ev_or (g : Gate) (w : List Bool) (a b : ℕ) (ho : g.op = GateOp.or)
    (hi : g.inputs = [a, b]) : evf g w = (w.getD a false || w.getD b false) := by
  unfold evf; rw [ho, hi]; simp [GateOp.eval]

theorem dg_and (g : Gate) (d : List ℕ) (a b : ℕ) (ho : g.op = GateOp.and)
    (hi : g.inputs = [a, b]) : dgf g d = d.getD a 0 + d.getD b 0 := by
  unfold dgf Gate.lineDegree
  rw [if_pos ho, hi]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem dg_or (g : Gate) (d : List ℕ) (a b : ℕ) (ho : g.op = GateOp.or)
    (hi : g.inputs = [a, b]) : dgf g d = max (d.getD a 0) (d.getD b 0) := by
  have hne : ¬ g.op = GateOp.and := by rw [ho]; intro h; cases h
  unfold dgf Gate.lineDegree
  rw [if_neg hne, hi]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  omega

def P (n : ℕ) (pre : List Gate) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ i ∈ g.inputs, i < n + pre.length)

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (suf : List Gate), gs = pre ++ g :: suf → P n pre g

theorem Good_snoc_inv (n : ℕ) (gs : List Gate) (g : Gate)
    (H : Good n (gs ++ [g])) : Good n gs ∧ P n gs g := by
  refine ⟨?_, H gs g [] rfl⟩
  intro pre g' suf h
  exact H pre g' (suf ++ [g]) (by rw [h]; simp)

theorem Good_snoc (n : ℕ) (es : List Gate) (e : Gate)
    (hG : Good n es) (hP : P n es e) : Good n (es ++ [e]) := by
  intro pre g suf h
  rcases List.eq_nil_or_concat' suf with hs | ⟨s, a, hs⟩
  · subst hs
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    have h3 : e = g := by simpa using h2
    subst h1; subst h3; exact hP
  · subst hs
    have h' : es ++ [e] = (pre ++ g :: s) ++ [a] := by rw [h]; simp
    obtain ⟨h1, _⟩ := List.append_inj' h' rfl
    exact hG pre g s h1

theorem dec (gs : List Gate) : ∀ (j : ℕ), j < gs.length →
    ∃ pre suf, gs = pre ++ gs.getD j ⟨GateOp.or, []⟩ :: suf ∧ pre.length = j := by
  induction gs with
  | nil => intro j hj; simp at hj
  | cons a t ih =>
    intro j hj
    cases j with
    | zero => exact ⟨[], t, rfl, rfl⟩
    | succ j =>
      obtain ⟨p, s, h1, h2⟩ := ih j (by simpa using hj)
      refine ⟨a :: p, s, ?_, by simp [h2]⟩
      rw [List.getD_cons_succ, List.cons_append]
      exact congrArg (List.cons a) h1

def X (iL iP : List ℕ) (pre : List Gate) (g : Gate) : Prop :=
  g.op = GateOp.and ∧ ¬ ((∃ i ∈ g.inputs, (run dgf pre iL).getD i 0 = 0) ∨
    (∀ h ∈ g.inputs, (run dgf pre iP).getD h 0 = 0))

def XS (iL iP : List ℕ) (gs : List Gate) : Set ℕ :=
  {j | j < gs.length ∧ X iL iP (gs.take j) (gs.getD j ⟨GateOp.or, []⟩)}

theorem mem_XS (iL iP : List ℕ) (gs : List Gate) (j : ℕ) :
    j ∈ XS iL iP gs ↔ (j < gs.length ∧ X iL iP (gs.take j) (gs.getD j ⟨GateOp.or, []⟩)) :=
  Iff.rfl

def AllI (R : List Gate → Gate → Prop) (gs : List Gate) : Prop :=
  ∀ j < gs.length, R (gs.take j) (gs.getD j ⟨GateOp.or, []⟩)

theorem snoc_take_lt (gs : List Gate) (g : Gate) (j : ℕ) (h : j < gs.length) :
    (gs ++ [g]).take j = gs.take j := List.take_append_of_le_length (le_of_lt h)

theorem snoc_getD_lt (gs : List Gate) (g d : Gate) (j : ℕ) (h : j < gs.length) :
    (gs ++ [g]).getD j d = gs.getD j d := List.getD_append _ _ _ _ h

theorem snoc_take_eq (gs : List Gate) (g : Gate) : (gs ++ [g]).take gs.length = gs := by simp

theorem snoc_getD_eq (gs : List Gate) (g d : Gate) : (gs ++ [g]).getD gs.length d = g := by
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]

theorem AllI_snoc (R : List Gate → Gate → Prop) (gs : List Gate) (g : Gate)
    (h : AllI R gs) (hg : R gs g) : AllI R (gs ++ [g]) := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j gs.length with h1 | h1
  · rw [snoc_take_lt gs g j h1, snoc_getD_lt gs g _ j h1]; exact h j h1
  · have hje : j = gs.length := by omega
    subst hje
    rw [snoc_take_eq, snoc_getD_eq]; exact hg

theorem XS_fin (iL iP : List ℕ) (gs : List Gate) : (XS iL iP gs).Finite :=
  Set.Finite.subset (Set.finite_Iio gs.length) (fun _ hj => hj.1)

theorem XS_pos (iL iP : List ℕ) (gs : List Gate) (g : Gate) (hx : X iL iP gs g) :
    XS iL iP (gs ++ [g]) = insert gs.length (XS iL iP gs) := by
  ext j
  rw [Set.mem_insert_iff, mem_XS, mem_XS, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨hj, hxj⟩
    rcases Nat.lt_or_ge j gs.length with h1 | h1
    · right
      rw [snoc_take_lt gs g j h1, snoc_getD_lt gs g _ j h1] at hxj
      exact ⟨h1, hxj⟩
    · left; omega
  · rintro (hje | ⟨h1, hxj⟩)
    · subst hje
      rw [snoc_take_eq, snoc_getD_eq]; exact ⟨by omega, hx⟩
    · rw [snoc_take_lt gs g j h1, snoc_getD_lt gs g _ j h1]; exact ⟨by omega, hxj⟩

theorem XS_neg (iL iP : List ℕ) (gs : List Gate) (g : Gate) (hx : ¬ X iL iP gs g) :
    XS iL iP (gs ++ [g]) = XS iL iP gs := by
  ext j
  rw [mem_XS, mem_XS, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨hj, hxj⟩
    rcases Nat.lt_or_ge j gs.length with h1 | h1
    · rw [snoc_take_lt gs g j h1, snoc_getD_lt gs g _ j h1] at hxj
      exact ⟨h1, hxj⟩
    · have hje : j = gs.length := by omega
      subst hje
      rw [snoc_take_eq, snoc_getD_eq] at hxj
      exact absurd hxj hx
  · rintro ⟨h1, hxj⟩
    rw [snoc_take_lt gs g j h1, snoc_getD_lt gs g _ j h1]; exact ⟨by omega, hxj⟩

theorem cnt_pos (iL iP : List ℕ) (gs : List Gate) (g : Gate) (hx : X iL iP gs g) :
    (XS iL iP (gs ++ [g])).ncard = (XS iL iP gs).ncard + 1 := by
  rw [XS_pos iL iP gs g hx]
  exact Set.ncard_insert_of_notMem
    (fun h => absurd ((mem_XS iL iP gs gs.length).mp h).1 (lt_irrefl _)) (XS_fin iL iP gs)

theorem cnt_neg (iL iP : List ℕ) (gs : List Gate) (g : Gate) (hx : ¬ X iL iP gs g) :
    (XS iL iP (gs ++ [g])).ncard = (XS iL iP gs).ncard := by
  rw [XS_neg iL iP gs g hx]

theorem notX_or (iL iP : List ℕ) (pre : List Gate) (a b : ℕ) :
    ¬ X iL iP pre ⟨GateOp.or, [a, b]⟩ := by
  intro hx
  obtain ⟨h1, _⟩ := hx
  cases h1

def Qp (iL iP : List ℕ) (z : List Bool) (pre : List Gate) (g : Gate) : Prop :=
  X iL iP pre g → ∀ i ∈ g.inputs, (run evf pre z).getD i false = false

def Zp (iF : List ℕ) (pre : List Gate) (g : Gate) : Prop :=
  ∀ i ∈ g.inputs, (run dgf pre iF).getD i 0 = 0

theorem inv_keep (iL iP : List ℕ) (z : List Bool) (gs es : List Gate) (g : Gate)
    (hle : es.length ≤ gs.length)
    (I2 : (XS iL iP es).ncard ≤ (XS iL iP gs).ncard)
    (I3 : ((XS iL iP es).ncard + 1 ≤ (XS iL iP gs).ncard ∧ es.length + 1 ≤ gs.length) ∨
      AllI (Qp iL iP z) gs) :
    (XS iL iP es).ncard ≤ (XS iL iP (gs ++ [g])).ncard ∧
    (((XS iL iP es).ncard + 1 ≤ (XS iL iP (gs ++ [g])).ncard ∧
        es.length + 1 ≤ (gs ++ [g]).length) ∨ AllI (Qp iL iP z) (gs ++ [g])) := by
  simp only [List.length_append, List.length_singleton]
  by_cases hx : X iL iP gs g
  · rw [cnt_pos iL iP gs g hx]
    exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  · rw [cnt_neg iL iP gs g hx]
    refine ⟨I2, ?_⟩
    rcases I3 with ⟨h1, h2⟩ | hQ
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr (AllI_snoc _ gs g hQ (fun h => absurd h hx))

theorem inv_new (iL iP : List ℕ) (z : List Bool) (gs es : List Gate) (g e : Gate)
    (I2 : (XS iL iP es).ncard ≤ (XS iL iP gs).ncard)
    (I3 : ((XS iL iP es).ncard + 1 ≤ (XS iL iP gs).ncard ∧ es.length + 1 ≤ gs.length) ∨
      AllI (Qp iL iP z) gs)
    (hxe : X iL iP es e → X iL iP gs g)
    (hq : X iL iP gs g → ∀ i ∈ g.inputs, (run evf gs z).getD i false = false) :
    (XS iL iP (es ++ [e])).ncard ≤ (XS iL iP (gs ++ [g])).ncard ∧
    (((XS iL iP (es ++ [e])).ncard + 1 ≤ (XS iL iP (gs ++ [g])).ncard ∧
        (es ++ [e]).length + 1 ≤ (gs ++ [g]).length) ∨ AllI (Qp iL iP z) (gs ++ [g])) := by
  simp only [List.length_append, List.length_singleton]
  have hle : (XS iL iP (es ++ [e])).ncard ≤ (XS iL iP es).ncard + 1 := by
    by_cases hx' : X iL iP es e
    · exact le_of_eq (cnt_pos iL iP es e hx')
    · exact le_trans (le_of_eq (cnt_neg iL iP es e hx')) (Nat.le_succ _)
  by_cases hx : X iL iP gs g
  · rw [cnt_pos iL iP gs g hx]
    refine ⟨by omega, ?_⟩
    rcases I3 with ⟨h1, h2⟩ | hQ
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (AllI_snoc _ gs g hQ (fun _ => hq hx))
  · rw [cnt_neg iL iP gs g hx, cnt_neg iL iP es e (fun h => hx (hxe h))]
    refine ⟨I2, ?_⟩
    rcases I3 with ⟨h1, h2⟩ | hQ
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr (AllI_snoc _ gs g hQ (fun h => absurd h hx))

theorem getD_false_of_all (l : List Bool) (h : ∀ x ∈ l, x = false) (k : ℕ) :
    l.getD k false = false := by
  rcases Nat.lt_or_ge k l.length with h1 | h1
  · rw [List.getD_eq_getElem _ _ h1]; exact h _ (List.getElem_mem h1)
  · exact List.getD_eq_default _ _ h1

theorem run_false (n : ℕ) (init : List Bool) (h0 : ∀ x ∈ init, x = false) :
    ∀ es : List Gate, Good n es → ∀ x ∈ run evf es init, x = false := by
  intro es
  induction es using List.reverseRecOn with
  | nil => intro _ x hx; exact h0 x hx
  | append_singleton es e ih =>
    intro HG x hx
    obtain ⟨HGs, ⟨hop, hlen⟩, _⟩ := Good_snoc_inv n es e HG
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    rw [run_snoc, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ih HGs x hx
    · rw [hx]
      have ha := getD_false_of_all _ (ih HGs) a
      have hb := getD_false_of_all _ (ih HGs) b
      rcases hop with hop | hop
      · rw [ev_and e _ a b hop hab, ha, Bool.false_and]
      · rw [ev_or e _ a b hop hab, ha, hb, Bool.false_or]

def Rel {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP iF : List ℕ) (gs es : List Gate)
    (w : ℕ) : Prop :=
  (∃ b : Bool, ∀ p, (run evf gs (r p)).getD w false = b) ∨
  (∃ k, k < n + es.length ∧
    (∀ p, (run evf es (f p)).getD k false = (run evf gs (r p)).getD w false) ∧
    (run dgf es iL).getD k 0 ≤ (run dgf gs iL).getD w 0 ∧
    (run dgf es iP).getD k 0 ≤ (run dgf gs iP).getD w 0 ∧
    (run dgf es iF).getD k 0 = 0)

theorem Rel_extD {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP iF : List ℕ)
    (hr : ∀ p, (r p).length = n) (hiL : iL.length = n) (hiP : iP.length = n)
    (gs es : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length)
    (h : Rel n r f iL iP iF gs es w) : Rel n r f iL iP iF (gs ++ [g]) es w := by
  have e1 : ∀ p, (run evf (gs ++ [g]) (r p)).getD w false = (run evf gs (r p)).getD w false :=
    fun p => run_stab evf gs [g] (r p) false w (by rw [hr]; exact hw)
  have e2 : (run dgf (gs ++ [g]) iL).getD w 0 = (run dgf gs iL).getD w 0 :=
    run_stab dgf gs [g] iL 0 w (by rw [hiL]; exact hw)
  have e3 : (run dgf (gs ++ [g]) iP).getD w 0 = (run dgf gs iP).getD w 0 :=
    run_stab dgf gs [g] iP 0 w (by rw [hiP]; exact hw)
  rcases h with ⟨b, hb⟩ | ⟨k, hk, hv, h1, h2, h3⟩
  · exact Or.inl ⟨b, fun p => by rw [e1]; exact hb p⟩
  · exact Or.inr ⟨k, hk, fun p => by rw [e1]; exact hv p, by rw [e2]; exact h1,
      by rw [e3]; exact h2, h3⟩

theorem Rel_extE {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP iF : List ℕ)
    (hf : ∀ p, (f p).length = n) (hiL : iL.length = n) (hiP : iP.length = n)
    (hiF : iF.length = n)
    (gs es : List Gate) (e : Gate) (w : ℕ)
    (h : Rel n r f iL iP iF gs es w) : Rel n r f iL iP iF gs (es ++ [e]) w := by
  rcases h with ⟨b, hb⟩ | ⟨k, hk, hv, h1, h2, h3⟩
  · exact Or.inl ⟨b, hb⟩
  · refine Or.inr ⟨k, by rw [List.length_append]; omega, fun p => ?_, ?_, ?_, ?_⟩
    · rw [run_stab evf es [e] (f p) false k (by rw [hf]; exact hk)]; exact hv p
    · rw [run_stab dgf es [e] iL 0 k (by rw [hiL]; exact hk)]; exact h1
    · rw [run_stab dgf es [e] iP 0 k (by rw [hiP]; exact hk)]; exact h2
    · rw [run_stab dgf es [e] iF 0 k (by rw [hiF]; exact hk)]; exact h3

theorem last_const {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP iF : List ℕ)
    (hr : ∀ p, (r p).length = n) (gs es : List Gate) (g : Gate) (b : Bool)
    (h : ∀ p, evf g (run evf gs (r p)) = b) :
    Rel n r f iL iP iF (gs ++ [g]) es (n + gs.length) := by
  refine Or.inl ⟨b, fun p => ?_⟩
  have e := run_last evf gs g (r p) false
  rw [hr] at e
  rw [e]; exact h p

theorem last_copy {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP iF : List ℕ)
    (hr : ∀ p, (r p).length = n) (hiL : iL.length = n) (hiP : iP.length = n)
    (gs es : List Gate) (g : Gate) (c : ℕ)
    (hc : Rel n r f iL iP iF gs es c)
    (hv : ∀ p, evf g (run evf gs (r p)) = (run evf gs (r p)).getD c false)
    (h1 : (run dgf gs iL).getD c 0 ≤ dgf g (run dgf gs iL))
    (h2 : (run dgf gs iP).getD c 0 ≤ dgf g (run dgf gs iP)) :
    Rel n r f iL iP iF (gs ++ [g]) es (n + gs.length) := by
  have e1 : ∀ p, (run evf (gs ++ [g]) (r p)).getD (n + gs.length) false
      = evf g (run evf gs (r p)) := by
    intro p
    have e := run_last evf gs g (r p) false
    rw [hr] at e; exact e
  have e2 : (run dgf (gs ++ [g]) iL).getD (n + gs.length) 0 = dgf g (run dgf gs iL) := by
    have e := run_last dgf gs g iL 0
    rw [hiL] at e; exact e
  have e3 : (run dgf (gs ++ [g]) iP).getD (n + gs.length) 0 = dgf g (run dgf gs iP) := by
    have e := run_last dgf gs g iP 0
    rw [hiP] at e; exact e
  rcases hc with ⟨b, hb⟩ | ⟨k, hk, hkv, k1, k2, k3⟩
  · exact Or.inl ⟨b, fun p => by rw [e1, hv, hb]⟩
  · exact Or.inr ⟨k, hk, fun p => by rw [e1, hv, hkv], by rw [e2]; exact le_trans k1 h1,
      by rw [e3]; exact le_trans k2 h2, k3⟩

theorem last_new {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP iF : List ℕ)
    (hr : ∀ p, (r p).length = n) (hf : ∀ p, (f p).length = n)
    (hiL : iL.length = n) (hiP : iP.length = n) (hiF : iF.length = n)
    (gs es : List Gate) (g e : Gate)
    (hv : ∀ p, evf e (run evf es (f p)) = evf g (run evf gs (r p)))
    (h1 : dgf e (run dgf es iL) ≤ dgf g (run dgf gs iL))
    (h2 : dgf e (run dgf es iP) ≤ dgf g (run dgf gs iP))
    (h3 : dgf e (run dgf es iF) = 0) :
    Rel n r f iL iP iF (gs ++ [g]) (es ++ [e]) (n + gs.length) := by
  refine Or.inr ⟨n + es.length, by rw [List.length_append, List.length_singleton]; omega,
    fun p => ?_, ?_, ?_, ?_⟩
  · have a1 := run_last evf gs g (r p) false
    have a2 := run_last evf es e (f p) false
    rw [hr] at a1; rw [hf] at a2
    rw [a1, a2]; exact hv p
  · have a1 := run_last dgf gs g iL 0
    have a2 := run_last dgf es e iL 0
    rw [hiL] at a1 a2
    rw [a1, a2]; exact h1
  · have a1 := run_last dgf gs g iP 0
    have a2 := run_last dgf es e iP 0
    rw [hiP] at a1 a2
    rw [a1, a2]; exact h2
  · have a2 := run_last dgf es e iF 0
    rw [hiF] at a2
    rw [a2]; exact h3

theorem main {ι : Type} (n : ℕ) (r f : ι → List Bool) (iL iP iF : List ℕ) (p0 : ι)
    (hr : ∀ p, (r p).length = n) (hf : ∀ p, (f p).length = n)
    (hiL : iL.length = n) (hiP : iP.length = n) (hiF : iF.length = n)
    (hf0 : ∀ x ∈ f p0, x = false)
    (hb : ∀ w < n, (∃ b : Bool, ∀ p, (r p).getD w false = b) ∨
      ((∀ p, (f p).getD w false = (r p).getD w false) ∧ iF.getD w 0 = 0)) :
    ∀ gs : List Gate, Good n gs → ∃ es : List Gate, Good n es ∧
      es.length ≤ gs.length ∧ (∀ w < n + gs.length, Rel n r f iL iP iF gs es w) ∧
      AllI (Zp iF) es ∧
      (XS iL iP es).ncard ≤ (XS iL iP gs).ncard ∧
      (((XS iL iP es).ncard + 1 ≤ (XS iL iP gs).ncard ∧ es.length + 1 ≤ gs.length) ∨
        AllI (Qp iL iP (r p0)) gs) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], ?_, le_refl _, ?_, ?_, le_refl _, Or.inr ?_⟩
    · intro pre g suf h
      simp at h
    · intro w hw
      have hw' : w < n := by simpa using hw
      rcases hb w hw' with ⟨b, hb'⟩ | ⟨he, h0⟩
      · exact Or.inl ⟨b, fun p => hb' p⟩
      · exact Or.inr ⟨w, hw, fun p => he p, le_refl _, le_refl _, h0⟩
    · intro j hj
      simp at hj
    · intro j hj
      simp at hj
  | append_singleton gs g ih =>
    intro HG
    obtain ⟨HGs, ⟨hop, hlen⟩, hrb⟩ := Good_snoc_inv n gs g HG
    obtain ⟨es, hE, hle, hrel, hZ, I2, I3⟩ := ih HGs
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have ha : a < n + gs.length := hrb a (by rw [hab]; simp)
    have hb2 : b < n + gs.length := hrb b (by rw [hab]; simp)
    have Ra := hrel a ha
    have Rb := hrel b hb2
    have hfal : ∀ k, (run evf es (f p0)).getD k false = false :=
      fun k => getD_false_of_all _ (run_false n (f p0) hf0 es hE) k
    have old : ∀ es' : List Gate, (∀ w < n + gs.length, Rel n r f iL iP iF gs es' w) →
        Rel n r f iL iP iF (gs ++ [g]) es' (n + gs.length) →
        ∀ w < n + (gs ++ [g]).length, Rel n r f iL iP iF (gs ++ [g]) es' w := by
      intro es' h1 h2 w hw
      rw [List.length_append, List.length_singleton] at hw
      rcases Nat.lt_or_ge w (n + gs.length) with h | h
      · exact Rel_extD n r f iL iP iF hr hiL hiP gs es' g w h (h1 w h)
      · have hwe : w = n + gs.length := by omega
        rw [hwe]; exact h2
    have keep : Rel n r f iL iP iF (gs ++ [g]) es (n + gs.length) →
        ∃ es' : List Gate, Good n es' ∧ es'.length ≤ (gs ++ [g]).length ∧
          (∀ w < n + (gs ++ [g]).length, Rel n r f iL iP iF (gs ++ [g]) es' w) ∧
          AllI (Zp iF) es' ∧
          (XS iL iP es').ncard ≤ (XS iL iP (gs ++ [g])).ncard ∧
          (((XS iL iP es').ncard + 1 ≤ (XS iL iP (gs ++ [g])).ncard ∧
            es'.length + 1 ≤ (gs ++ [g]).length) ∨ AllI (Qp iL iP (r p0)) (gs ++ [g])) := by
      intro h
      obtain ⟨k1, k2⟩ := inv_keep iL iP (r p0) gs es g hle I2 I3
      exact ⟨es, hE, by rw [List.length_append, List.length_singleton]; omega,
        old es hrel h, hZ, k1, k2⟩
    have mk : ∀ e : Gate, P n es e → Zp iF es e →
        Rel n r f iL iP iF (gs ++ [g]) (es ++ [e]) (n + gs.length) →
        (X iL iP es e → X iL iP gs g) →
        (X iL iP gs g → ∀ i ∈ g.inputs, (run evf gs (r p0)).getD i false = false) →
        ∃ es' : List Gate, Good n es' ∧ es'.length ≤ (gs ++ [g]).length ∧
          (∀ w < n + (gs ++ [g]).length, Rel n r f iL iP iF (gs ++ [g]) es' w) ∧
          AllI (Zp iF) es' ∧
          (XS iL iP es').ncard ≤ (XS iL iP (gs ++ [g])).ncard ∧
          (((XS iL iP es').ncard + 1 ≤ (XS iL iP (gs ++ [g])).ncard ∧
            es'.length + 1 ≤ (gs ++ [g]).length) ∨ AllI (Qp iL iP (r p0)) (gs ++ [g])) := by
      intro e hP hZe hR hxe hq
      obtain ⟨k1, k2⟩ := inv_new iL iP (r p0) gs es g e I2 I3 hxe hq
      refine ⟨es ++ [e], Good_snoc n es e hE hP, ?_, ?_, AllI_snoc _ es e hZ hZe, k1, k2⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · exact old (es ++ [e])
          (fun w hw => Rel_extE n r f iL iP iF hf hiL hiP hiF gs es e w (hrel w hw)) hR
    have hqq : ∀ ka kb : ℕ,
        (∀ p, (run evf es (f p)).getD ka false = (run evf gs (r p)).getD a false) →
        (∀ p, (run evf es (f p)).getD kb false = (run evf gs (r p)).getD b false) →
        X iL iP gs g → ∀ i ∈ g.inputs, (run evf gs (r p0)).getD i false = false := by
      intro ka kb hva hvb _ i hi
      rw [hab] at hi
      have hi' : i = a ∨ i = b := by simpa using hi
      rcases hi' with h | h
      · rw [h, ← hva p0]; exact hfal ka
      · rw [h, ← hvb p0]; exact hfal kb
    rcases hop with hop | hop
    · have hev : ∀ w : List Bool, evf g w = (w.getD a false && w.getD b false) :=
        fun w => ev_and g w a b hop hab
      have hdg : ∀ d : List ℕ, dgf g d = d.getD a 0 + d.getD b 0 :=
        fun d => dg_and g d a b hop hab
      rcases hrel a ha with ⟨ba, hca⟩ | ⟨ka, hka, hva, a1, a2, a3⟩
      · cases ba with
        | false =>
          exact keep (last_const n r f iL iP iF hr gs es g false
            (fun p => by rw [hev, hca p, Bool.false_and]))
        | true =>
          exact keep (last_copy n r f iL iP iF hr hiL hiP gs es g b Rb
            (fun p => by rw [hev, hca p, Bool.true_and])
            (by rw [hdg]; omega) (by rw [hdg]; omega))
      · rcases hrel b hb2 with ⟨bb, hcb⟩ | ⟨kb, hkb, hvb, b1, b2, b3⟩
        · cases bb with
          | false =>
            exact keep (last_const n r f iL iP iF hr gs es g false
              (fun p => by rw [hev, hcb p, Bool.and_false]))
          | true =>
            exact keep (last_copy n r f iL iP iF hr hiL hiP gs es g a Ra
              (fun p => by rw [hev, hcb p, Bool.and_true])
              (by rw [hdg]; omega) (by rw [hdg]; omega))
        · apply mk ⟨GateOp.and, [ka, kb]⟩
          · refine ⟨⟨Or.inl rfl, rfl⟩, ?_⟩
            intro i hi
            have hi' : i = ka ∨ i = kb := by simpa using hi
            rcases hi' with h | h
            · rw [h]; exact hka
            · rw [h]; exact hkb
          · intro i hi
            have hi' : i = ka ∨ i = kb := by simpa using hi
            rcases hi' with h | h
            · rw [h]; exact a3
            · rw [h]; exact b3
          · apply last_new n r f iL iP iF hr hf hiL hiP hiF gs es g _
            · intro p
              rw [hev, ev_and ⟨GateOp.and, [ka, kb]⟩ _ ka kb rfl rfl, hva p, hvb p]
            · rw [hdg, dg_and ⟨GateOp.and, [ka, kb]⟩ _ ka kb rfl rfl]; omega
            · rw [hdg, dg_and ⟨GateOp.and, [ka, kb]⟩ _ ka kb rfl rfl]; omega
            · rw [dg_and ⟨GateOp.and, [ka, kb]⟩ _ ka kb rfl rfl]; omega
          · intro hxe
            obtain ⟨_, hx2⟩ := hxe
            refine ⟨hop, fun hk => hx2 ?_⟩
            rcases hk with ⟨i, hi, h0⟩ | hall
            · rw [hab] at hi
              have hi' : i = a ∨ i = b := by simpa using hi
              rcases hi' with h | h
              · rw [h] at h0
                exact Or.inl ⟨ka, by simp, by omega⟩
              · rw [h] at h0
                exact Or.inl ⟨kb, by simp, by omega⟩
            · have h0a := hall a (by rw [hab]; simp)
              have h0b := hall b (by rw [hab]; simp)
              refine Or.inr (fun h hh => ?_)
              have hh' : h = ka ∨ h = kb := by simpa using hh
              rcases hh' with e | e
              · rw [e]; omega
              · rw [e]; omega
          · exact hqq ka kb hva hvb
    · have hev : ∀ w : List Bool, evf g w = (w.getD a false || w.getD b false) :=
        fun w => ev_or g w a b hop hab
      have hdg : ∀ d : List ℕ, dgf g d = max (d.getD a 0) (d.getD b 0) :=
        fun d => dg_or g d a b hop hab
      rcases hrel a ha with ⟨ba, hca⟩ | ⟨ka, hka, hva, a1, a2, a3⟩
      · cases ba with
        | true =>
          exact keep (last_const n r f iL iP iF hr gs es g true
            (fun p => by rw [hev, hca p, Bool.true_or]))
        | false =>
          exact keep (last_copy n r f iL iP iF hr hiL hiP gs es g b Rb
            (fun p => by rw [hev, hca p, Bool.false_or])
            (by rw [hdg]; exact le_max_right _ _) (by rw [hdg]; exact le_max_right _ _))
      · rcases hrel b hb2 with ⟨bb, hcb⟩ | ⟨kb, hkb, hvb, b1, b2, b3⟩
        · cases bb with
          | true =>
            exact keep (last_const n r f iL iP iF hr gs es g true
              (fun p => by rw [hev, hcb p, Bool.or_true]))
          | false =>
            exact keep (last_copy n r f iL iP iF hr hiL hiP gs es g a Ra
              (fun p => by rw [hev, hcb p, Bool.or_false])
              (by rw [hdg]; exact le_max_left _ _) (by rw [hdg]; exact le_max_left _ _))
        · apply mk ⟨GateOp.or, [ka, kb]⟩
          · refine ⟨⟨Or.inr rfl, rfl⟩, ?_⟩
            intro i hi
            have hi' : i = ka ∨ i = kb := by simpa using hi
            rcases hi' with h | h
            · rw [h]; exact hka
            · rw [h]; exact hkb
          · intro i hi
            have hi' : i = ka ∨ i = kb := by simpa using hi
            rcases hi' with h | h
            · rw [h]; exact a3
            · rw [h]; exact b3
          · apply last_new n r f iL iP iF hr hf hiL hiP hiF gs es g _
            · intro p
              rw [hev, ev_or ⟨GateOp.or, [ka, kb]⟩ _ ka kb rfl rfl, hva p, hvb p]
            · rw [hdg, dg_or ⟨GateOp.or, [ka, kb]⟩ _ ka kb rfl rfl]; exact max_le_max a1 b1
            · rw [hdg, dg_or ⟨GateOp.or, [ka, kb]⟩ _ ka kb rfl rfl]; exact max_le_max a2 b2
            · rw [dg_or ⟨GateOp.or, [ka, kb]⟩ _ ka kb rfl rfl]; omega
          · intro hxe
            exact absurd hxe (notX_or iL iP es ka kb)
          · exact hqq ka kb hva hvb

theorem toGood (n : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : NestedCover.ReadsBack n C) : Good n C.gates := by
  intro pre g suf h
  have hj : pre.length < C.gates.length := by
    rw [h, List.length_append, List.length_cons]; omega
  have hga : NestedCover.gateAt C pre.length = g := by
    unfold NestedCover.gateAt
    rw [h, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
  have hin : ∀ i ∈ g.inputs, i < n + pre.length := by
    intro i hi
    exact hrb pre.length hj i (by rw [hga]; exact hi)
  unfold P
  exact ⟨hg g (by rw [h]; simp), hin⟩

theorem fromGood (n : ℕ) (es : List Gate) (o : ℕ) (H : Good n es) :
    (∀ g ∈ (Circuit.mk es o).gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      NestedCover.ReadsBack n (Circuit.mk es o) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨s, t, h⟩ := List.append_of_mem hg
    obtain ⟨hA, _⟩ := H s g t h
    exact hA
  · intro j hj i hi
    obtain ⟨pre, suf, h1, h2⟩ := dec es j hj
    obtain ⟨_, hB⟩ := H pre _ suf h1
    have hlt := hB i hi
    rw [h2] at hlt; exact hlt

theorem or_congr_mem (l : List ℕ) (A A' B B' : ℕ → ℕ) (hA : ∀ i ∈ l, A i = A' i)
    (hB : ∀ i ∈ l, B i = B' i) :
    ((∃ i ∈ l, A i = 0) ∨ (∀ h ∈ l, B h = 0)) ↔ ((∃ i ∈ l, A' i = 0) ∨ (∀ h ∈ l, B' h = 0)) := by
  constructor
  · rintro (⟨i, hi, h0⟩ | hall)
    · exact Or.inl ⟨i, hi, by rw [← hA i hi]; exact h0⟩
    · exact Or.inr (fun h hh => by rw [← hB h hh]; exact hall h hh)
  · rintro (⟨i, hi, h0⟩ | hall)
    · exact Or.inl ⟨i, hi, by rw [hA i hi]; exact h0⟩
    · exact Or.inr (fun h hh => by rw [hB h hh]; exact hall h hh)

theorem cross_iff (n : ℕ) (L Pm : Finset ℕ) (E : Circuit) (hrb : NestedCover.ReadsBack n E)
    (j : ℕ) (hj : j < E.gates.length) :
    ((NestedCover.gateAt E j).op = GateOp.and ∧
      ¬ ((∃ i ∈ (NestedCover.gateAt E j).inputs, (E.lineDegrees n L).getD i 0 = 0) ∨
        (∀ h ∈ (NestedCover.gateAt E j).inputs, (E.lineDegrees n Pm).getD h 0 = 0))) ↔
    X (ini n L) (ini n Pm) (E.gates.take j) (E.gates.getD j ⟨GateOp.or, []⟩) := by
  have key : ∀ (M : Finset ℕ) (i : ℕ), i ∈ (NestedCover.gateAt E j).inputs →
      (E.lineDegrees n M).getD i 0 = (run dgf (E.gates.take j) (ini n M)).getD i 0 := by
    intro M i hi
    have hlt := hrb j hj i hi
    have h := run_stab dgf (E.gates.take j) (E.gates.drop j) (ini n M) 0 i
      (by rw [ini_len, List.length_take]; omega)
    rw [List.take_append_drop] at h
    exact h
  have e := or_congr_mem (NestedCover.gateAt E j).inputs
    (fun i => (E.lineDegrees n L).getD i 0)
    (fun i => (run dgf (E.gates.take j) (ini n L)).getD i 0)
    (fun i => (E.lineDegrees n Pm).getD i 0)
    (fun i => (run dgf (E.gates.take j) (ini n Pm)).getD i 0) (key L) (key Pm)
  unfold X
  exact and_congr Iff.rfl (not_congr e)

theorem bridge (n : ℕ) (L Pm : Finset ℕ) (E : Circuit) (hrb : NestedCover.ReadsBack n E) :
    {j : ℕ | j < E.gates.length ∧ (NestedCover.gateAt E j).op = GateOp.and ∧
      ¬ ((∃ i ∈ (NestedCover.gateAt E j).inputs, (E.lineDegrees n L).getD i 0 = 0) ∨
        (∀ h ∈ (NestedCover.gateAt E j).inputs, (E.lineDegrees n Pm).getD h 0 = 0))} =
    XS (ini n L) (ini n Pm) E.gates := by
  ext j
  constructor
  · rintro ⟨hj, h⟩
    exact (mem_XS _ _ _ _).mpr ⟨hj, (cross_iff n L Pm E hrb j hj).mp h⟩
  · intro h
    obtain ⟨hj, hx⟩ := (mem_XS _ _ _ _).mp h
    exact ⟨hj, (cross_iff n L Pm E hrb j hj).mpr hx⟩

theorem take_succ' (l : List Gate) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l.getD k ⟨GateOp.or, []⟩] := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.take_succ_eq_append_getElem hk

theorem runs_eq (gs vs : List Gate) (init : List Bool) (hlen : vs.length = gs.length)
    (H : ∀ j < gs.length, evf (vs.getD j ⟨GateOp.or, []⟩) (run evf (gs.take j) init) =
      evf (gs.getD j ⟨GateOp.or, []⟩) (run evf (gs.take j) init)) :
    run evf vs init = run evf gs init := by
  have key : ∀ k, k ≤ gs.length → run evf (vs.take k) init = run evf (gs.take k) init := by
    intro k
    induction k with
    | zero => intro _; simp [run]
    | succ k ih =>
      intro hk
      have hk' : k < gs.length := by omega
      rw [take_succ' vs k (by omega), take_succ' gs k hk', run_snoc, run_snoc, ih (by omega),
        H k hk']
  have h := key gs.length (le_refl _)
  have h1 : vs.take gs.length = vs := by rw [← hlen]; simp
  have h2 : gs.take gs.length = gs := by simp
  rw [h1, h2] at h
  exact h

theorem ofFn_getD' {m : ℕ} (F : Fin m → Gate) (j : ℕ) (hj : j < m) :
    (List.ofFn F).getD j ⟨GateOp.or, []⟩ = F ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem cross_false (g : Gate) (w : List Bool) (s : ℕ) (hs : s < 2) (hop : g.op = GateOp.and)
    (hlen : g.inputs.length = 2) (hin : ∀ i ∈ g.inputs, w.getD i false = false) :
    evf ⟨GateOp.or, [g.inputs.getD s 0, g.inputs.getD s 0]⟩ w = evf g w := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have hcm : g.inputs.getD s 0 ∈ g.inputs := by
    rw [hab]
    have h01 : s = 0 ∨ s = 1 := by omega
    rcases h01 with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [ev_or ⟨GateOp.or, [g.inputs.getD s 0, g.inputs.getD s 0]⟩ w _ _ rfl rfl, hin _ hcm,
    ev_and g w a b hop hab, hin a (by rw [hab]; simp), Bool.false_or, Bool.false_and]

theorem view_contra (iL iP : List ℕ) (C : Circuit) (z : List Bool)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hQ : AllI (Qp iL iP z) C.gates)
    (F : Fin C.gates.length → Gate) (sel : ℕ → ℕ) (hsel : ∀ j, sel j < 2)
    (hF : ∀ j : Fin C.gates.length,
      (X iL iP (C.gates.take j) (C.gates.getD j ⟨GateOp.or, []⟩) →
        F j = ⟨GateOp.or, [(C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (sel j) 0,
          (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (sel j) 0]⟩) ∧
      (¬ X iL iP (C.gates.take j) (C.gates.getD j ⟨GateOp.or, []⟩) →
        F j = C.gates.getD j ⟨GateOp.or, []⟩))
    (hv : (Circuit.mk (List.ofFn F) C.output).eval z = true) (hc : C.eval z = false) :
    False := by
  have e : run evf (List.ofFn F) z = run evf C.gates z := by
    apply runs_eq C.gates (List.ofFn F) z (by simp)
    intro j hj
    rw [ofFn_getD' F j hj]
    by_cases hx : X iL iP (C.gates.take j) (C.gates.getD j ⟨GateOp.or, []⟩)
    · have hF1 : F ⟨j, hj⟩ = ⟨GateOp.or,
          [(C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (sel j) 0,
            (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (sel j) 0]⟩ := (hF ⟨j, hj⟩).1 hx
      rw [hF1]
      have hin := hQ j hj hx
      have hmem : C.gates.getD j ⟨GateOp.or, []⟩ ∈ C.gates := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      obtain ⟨_, hlen⟩ := hg _ hmem
      obtain ⟨hop, _⟩ := hx
      exact cross_false _ _ (sel j) (hsel j) hop hlen hin
    · have hF2 : F ⟨j, hj⟩ = C.gates.getD j ⟨GateOp.or, []⟩ := (hF ⟨j, hj⟩).2 hx
      rw [hF2]
  have hv' : (run evf (List.ofFn F) z).getD C.output false = true := hv
  have hc' : (run evf C.gates z).getD C.output false = false := hc
  rw [e, hc'] at hv'
  cases hv'

theorem ofFn_getD {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def rI (N : ℕ) (S W : Finset (Fin N)) (pi nu : Fin N → Bool)
    (p : (Fin N → Bool) × (Fin N → Bool)) : List Bool :=
  List.ofFn (Fin.append (fun u => if u ∈ S then p.1 u else pi u)
    (fun t => if t ∈ W then p.2 t else nu t))

def fI (N : ℕ) (p : (Fin N → Bool) × (Fin N → Bool)) : List Bool :=
  List.ofFn (Fin.append p.1 p.2)

def FixS (N : ℕ) (S W : Finset (Fin N)) : Finset ℕ :=
  Finset.image (fun p : Fin N => (p : ℕ)) Sᶜ ∪ Finset.image (fun l : Fin N => N + (l : ℕ)) Wᶜ

theorem notmem_left (N : ℕ) (S W : Finset (Fin N)) (i : Fin N) (hi : i ∈ S) :
    (i : ℕ) ∉ FixS N S W := by
  unfold FixS
  intro h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    have hai : a = i := Fin.ext hae
    rw [hai] at ha
    exact (Finset.mem_compl.mp ha) hi
  · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    have hae' : N + (a : ℕ) = (i : ℕ) := hae
    have := i.isLt
    omega

theorem notmem_right (N : ℕ) (S W : Finset (Fin N)) (i : Fin N) (hi : i ∈ W) :
    N + (i : ℕ) ∉ FixS N S W := by
  unfold FixS
  intro h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    have hae' : (a : ℕ) = N + (i : ℕ) := hae
    have := a.isLt
    omega
  · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    have hae' : N + (a : ℕ) = N + (i : ℕ) := hae
    have hai : a = i := Fin.ext (by omega)
    rw [hai] at ha
    exact (Finset.mem_compl.mp ha) hi

theorem base (N : ℕ) (S W : Finset (Fin N)) (pi nu : Fin N → Bool) :
    ∀ w < N + N, (∃ b : Bool, ∀ p, (rI N S W pi nu p).getD w false = b) ∨
      ((∀ p, (fI N p).getD w false = (rI N S W pi nu p).getD w false) ∧
        (ini (N + N) (FixS N S W)).getD w 0 = 0) := by
  intro w hw
  have key : ∀ v : Fin (N + N),
      (∃ b : Bool, ∀ p : (Fin N → Bool) × (Fin N → Bool),
        Fin.append (fun u => if u ∈ S then p.1 u else pi u)
          (fun t => if t ∈ W then p.2 t else nu t) v = b) ∨
      ((∀ p : (Fin N → Bool) × (Fin N → Bool),
        Fin.append p.1 p.2 v = Fin.append (fun u => if u ∈ S then p.1 u else pi u)
          (fun t => if t ∈ W then p.2 t else nu t) v) ∧ (v : ℕ) ∉ FixS N S W) := by
    intro v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) v
    · by_cases hi : i ∈ S
      · refine Or.inr ⟨fun p => ?_, ?_⟩
        · rw [Fin.append_left, Fin.append_left]
          simp [hi]
        · rw [Fin.coe_castAdd]
          exact notmem_left N S W i hi
      · refine Or.inl ⟨pi i, fun p => ?_⟩
        rw [Fin.append_left]
        simp [hi]
    · by_cases hi : i ∈ W
      · refine Or.inr ⟨fun p => ?_, ?_⟩
        · rw [Fin.append_right, Fin.append_right]
          simp [hi]
        · rw [Fin.coe_natAdd]
          exact notmem_right N S W i hi
      · refine Or.inl ⟨nu i, fun p => ?_⟩
        rw [Fin.append_right]
        simp [hi]
  rcases key ⟨w, hw⟩ with ⟨b, hb⟩ | ⟨he, hn⟩
  · refine Or.inl ⟨b, fun p => ?_⟩
    unfold rI
    rw [ofFn_getD _ w hw]
    exact hb p
  · refine Or.inr ⟨fun p => ?_, ini_getD (N + N) (FixS N S W) w hw hn⟩
    unfold rI fI
    rw [ofFn_getD _ w hw, ofFn_getD _ w hw]
    exact he p

theorem rI_len (N : ℕ) (S W : Finset (Fin N)) (pi nu : Fin N → Bool)
    (p : (Fin N → Bool) × (Fin N → Bool)) : (rI N S W pi nu p).length = N + N := by
  simp [rI]

theorem fI_len (N : ℕ) (p : (Fin N → Bool) × (Fin N → Bool)) : (fI N p).length = N + N := by
  simp [fI]

theorem fI_false (N : ℕ) :
    ∀ x ∈ fI N ((fun _ => false), (fun _ => false)), x = false := by
  intro x hx
  unfold fI at hx
  rw [List.mem_ofFn] at hx
  obtain ⟨v, hv⟩ := hx
  rw [← hv]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) v
  · exact Fin.append_left _ _ i
  · exact Fin.append_right _ _ i

theorem ev_oob (D : Circuit) (n : ℕ) (ho : n + D.gates.length ≤ D.output) (z : List Bool)
    (hz : z.length = n) : D.eval z = false := by
  show (run evf D.gates z).getD D.output false = false
  apply List.getD_eq_default
  rw [run_len, hz]; exact ho

theorem final (N m : ℕ) (C : Circuit) (S W : Finset (Fin N)) (pi nu : Fin N → Bool)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : NestedCover.ReadsBack (N + N) C)
    (hcnt : (XS (ini (N + N) (Finset.Ico N (N + N))) (ini (N + N) (Finset.range N))
      C.gates).ncard ≤ m + 1)
    (hQ : ¬ AllI (Qp (ini (N + N) (Finset.Ico N (N + N))) (ini (N + N) (Finset.range N))
      (rI N S W pi nu ((fun _ => false), (fun _ => false)))) C.gates)
    (hC0 : C.eval (rI N S W pi nu ((fun _ => false), (fun _ => false))) = false)
    (hne : ∃ x y : Fin N → Bool, C.eval (rI N S W pi nu (x, y)) = true) :
    ∃ D : Circuit,
      ((∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        NestedCover.ReadsBack (N + N) D) ∧
      (XS (ini (N + N) (Finset.Ico N (N + N))) (ini (N + N) (Finset.range N))
        D.gates).ncard ≤ m ∧
      D.size ≤ C.size ∧
      (0 < D.gates.length ∧
        (∀ j < D.gates.length, ∀ i ∈ (NestedCover.gateAt D j).inputs,
          (D.lineDegrees (N + N) (FixS N S W)).getD i 0 = 0) ∧
        (D.lineDegrees (N + N) (FixS N S W)).getD D.output 0 = 0) ∧
      ∀ x y : Fin N → Bool, D.eval (fI N (x, y)) = C.eval (rI N S W pi nu (x, y)) := by
  have hG := toGood (N + N) C hg hrb
  obtain ⟨es, hE, hle, hrel, hZ, I2, I3⟩ := main (N + N) (rI N S W pi nu) (fI N)
    (ini (N + N) (Finset.Ico N (N + N))) (ini (N + N) (Finset.range N))
    (ini (N + N) (FixS N S W)) ((fun _ => false), (fun _ => false))
    (rI_len N S W pi nu) (fI_len N) (ini_len _ _) (ini_len _ _) (ini_len _ _)
    (fI_false N) (base N S W pi nu) C.gates hG
  obtain ⟨x, y, hxy⟩ := hne
  rcases I3 with ⟨J1, J2⟩ | hQ'
  swap
  · exact absurd hQ' hQ
  rcases Nat.lt_or_ge C.output (N + N + C.gates.length) with ho | ho
  swap
  · exfalso
    have h0 := ev_oob C (N + N) ho (rI N S W pi nu (x, y)) (rI_len N S W pi nu (x, y))
    rw [h0] at hxy
    cases hxy
  rcases hrel C.output ho with ⟨b, hb⟩ | ⟨k, hk, hv, _, _, hk0⟩
  · exfalso
    have h1 : C.eval (rI N S W pi nu ((fun _ => false), (fun _ => false))) = b := hb _
    have h2 : C.eval (rI N S W pi nu (x, y)) = b := hb _
    rw [hC0] at h1
    rw [hxy, ← h1] at h2
    cases h2
  · have hPe : P (N + N) es ⟨GateOp.or, [k, k]⟩ := by
      refine ⟨⟨Or.inr rfl, rfl⟩, ?_⟩
      intro i hi
      have hi' : i = k := by simpa using hi
      rw [hi']; exact hk
    have hZe : Zp (ini (N + N) (FixS N S W)) es ⟨GateOp.or, [k, k]⟩ := by
      intro i hi
      have hi' : i = k := by simpa using hi
      rw [hi']; exact hk0
    have hGD := Good_snoc (N + N) es _ hE hPe
    have hZD := AllI_snoc _ es _ hZ hZe
    have hF := fromGood (N + N) (es ++ [⟨GateOp.or, [k, k]⟩]) (N + N + es.length) hGD
    refine ⟨⟨es ++ [⟨GateOp.or, [k, k]⟩], N + N + es.length⟩, hF, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · show (XS (ini (N + N) (Finset.Ico N (N + N))) (ini (N + N) (Finset.range N))
        (es ++ [⟨GateOp.or, [k, k]⟩])).ncard ≤ m
      rw [cnt_neg _ _ es _ (notX_or _ _ es k k)]
      omega
    · show (es ++ [(⟨GateOp.or, [k, k]⟩ : Gate)]).length ≤ C.gates.length
      rw [List.length_append, List.length_singleton]; exact J2
    · show 0 < (es ++ [(⟨GateOp.or, [k, k]⟩ : Gate)]).length
      rw [List.length_append, List.length_singleton]; omega
    · intro j hj i hi
      have hj' : j < (es ++ [(⟨GateOp.or, [k, k]⟩ : Gate)]).length := hj
      have h1 := hZD j hj' i hi
      have hlt := hF.2 j hj i hi
      have h := run_stab dgf ((es ++ [(⟨GateOp.or, [k, k]⟩ : Gate)]).take j)
        ((es ++ [(⟨GateOp.or, [k, k]⟩ : Gate)]).drop j) (ini (N + N) (FixS N S W)) 0 i
        (by rw [ini_len, List.length_take]; omega)
      rw [List.take_append_drop] at h
      exact h.trans h1
    · have e := run_last dgf es ⟨GateOp.or, [k, k]⟩ (ini (N + N) (FixS N S W)) 0
      rw [ini_len] at e
      show (run dgf (es ++ [⟨GateOp.or, [k, k]⟩]) (ini (N + N) (FixS N S W))).getD
        (N + N + es.length) 0 = 0
      rw [e, dg_or ⟨GateOp.or, [k, k]⟩ _ k k rfl rfl]
      omega
    · intro x' y'
      have e := run_last evf es ⟨GateOp.or, [k, k]⟩ (fI N (x', y')) false
      rw [fI_len] at e
      show (run evf (es ++ [⟨GateOp.or, [k, k]⟩]) (fI N (x', y'))).getD
        (N + N + es.length) false =
        (run evf C.gates (rI N S W pi nu (x', y'))).getD C.output false
      rw [e, ev_or ⟨GateOp.or, [k, k]⟩ _ k k rfl rfl, hv (x', y'), Bool.or_self]

end PEqualNP.Outside.L_meta_1833

theorem PEqualNP.Outside.L_meta_1833 : ∀ (Nlv15 mlv15 : ℕ) (Clv15 : PEqualNP.CircuitLowerBounds.Circuit) (Slv15 Wlv15 : Finset (Fin Nlv15)) (pilv15 nulv15 : Fin Nlv15 → Bool) (sglv15 : ℕ → Fin 2), ((∀ glv15 ∈ Clv15.gates, (glv15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Clv15) → Set.ncard {jlv15 : ℕ | jlv15 < Clv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15 0 = 0) ∨ (∀ hlv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15 0 = 0))} ≤ mlv15 + 1 → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15x1 : Fin Clv15.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x1 0 = 0) ∨ (∀ hlv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val))) Clv15.output) (Fin.append (fun plv15 : Fin Nlv15 => if plv15 ∈ Slv15 then (fun ulv15 : Fin Nlv15 => false) plv15 else pilv15 plv15) (fun llv15 : Fin Nlv15 => if llv15 ∈ Wlv15 then (fun ulv15x1 : Fin Nlv15 => false) llv15 else nulv15 llv15)) = true → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x1 : Fin Nlv15 => if plv15x1 ∈ Slv15 then (fun ulv15x2 : Fin Nlv15 => false) plv15x1 else pilv15 plv15x1) (fun llv15x1 : Fin Nlv15 => if llv15x1 ∈ Wlv15 then (fun ulv15x3 : Fin Nlv15 => false) llv15x1 else nulv15 llv15x1)) = false → (∃ xlv15 ylv15 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x2 : Fin Nlv15 => if plv15x2 ∈ Slv15 then xlv15 plv15x2 else pilv15 plv15x2) (fun llv15x2 : Fin Nlv15 => if llv15x2 ∈ Wlv15 then ylv15 llv15x2 else nulv15 llv15x2)) = true) → ∃ Dlv15 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15x1 ∈ Dlv15.gates, (glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Dlv15) ∧ Set.ncard {jlv15x2 : ℕ | jlv15x2 < Dlv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x2 0 = 0) ∨ (∀ hlv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x2 0 = 0))} ≤ mlv15 ∧ Dlv15.size ≤ Clv15.size ∧ (0 < Dlv15.gates.length ∧ (∀ jlv15x3 < Dlv15.gates.length, ∀ ilv15x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x3).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x3 : Fin Nlv15 => (plv15x3 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x3 : Fin Nlv15 => Nlv15 + (llv15x3 : ℕ)) (Wlv15)ᶜ)).getD ilv15x3 0 = 0) ∧ (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x4 : Fin Nlv15 => (plv15x4 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x4 : Fin Nlv15 => Nlv15 + (llv15x4 : ℕ)) (Wlv15)ᶜ)).getD Dlv15.output 0 = 0) ∧ ∀ xlv15x1 ylv15x1 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Dlv15 (Fin.append xlv15x1 ylv15x1) = PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x5 : Fin Nlv15 => if plv15x5 ∈ Slv15 then xlv15x1 plv15x5 else pilv15 plv15x5) (fun llv15x5 : Fin Nlv15 => if llv15x5 ∈ Wlv15 then ylv15x1 llv15x5 else nulv15 llv15x5)) := by
  intro N m C S W pi nu sg hAO hcnt hview hC0 hne
  obtain ⟨hg, hrb⟩ := hAO
  have hcnt' := le_of_eq_of_le (congrArg Set.ncard
    (PEqualNP.Outside.L_meta_1833.bridge (N + N) (Finset.Ico N (N + N)) (Finset.range N)
      C hrb).symm) hcnt
  have hQ : ¬ PEqualNP.Outside.L_meta_1833.AllI (PEqualNP.Outside.L_meta_1833.Qp
      (PEqualNP.Outside.L_meta_1833.ini (N + N) (Finset.Ico N (N + N)))
      (PEqualNP.Outside.L_meta_1833.ini (N + N) (Finset.range N))
      (PEqualNP.Outside.L_meta_1833.rI N S W pi nu ((fun _ => false), (fun _ => false))))
      C.gates := by
    intro hQ
    refine PEqualNP.Outside.L_meta_1833.view_contra _ _ C _ hg hQ _ (fun j => (sg j).val)
      (fun j => (sg j).isLt) ?_ hview hC0
    intro j
    constructor
    · intro hx
      exact if_pos ((PEqualNP.Outside.L_meta_1833.cross_iff (N + N) (Finset.Ico N (N + N))
        (Finset.range N) C hrb j.val j.isLt).mpr hx)
    · intro hx
      exact if_neg (fun h => hx ((PEqualNP.Outside.L_meta_1833.cross_iff (N + N)
        (Finset.Ico N (N + N)) (Finset.range N) C hrb j.val j.isLt).mp h))
  obtain ⟨D, h1, h2, h3, h4, h5⟩ := PEqualNP.Outside.L_meta_1833.final N m C S W pi nu hg hrb
    hcnt' hQ hC0 hne
  exact ⟨D, h1, le_of_eq_of_le (congrArg Set.ncard
    (PEqualNP.Outside.L_meta_1833.bridge (N + N) (Finset.Ico N (N + N)) (Finset.range N)
      D h1.2)) h2, h3, h4, fun x y => h5 x y⟩
