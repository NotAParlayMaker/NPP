import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1042_aux

open PEqualNP.CircuitLowerBounds

abbrev F (n : ℕ) := Finset (Fin n) → Bool

def line {n : ℕ} (s : Finset (Fin n)) : F n := fun x => decide (∃ p ∈ s, p ∈ x)
def point {n : ℕ} (p : Fin n) : F n := fun x => decide (p ∈ x)
def below {n : ℕ} (f g : F n) : Prop := ∀ x, f x = true → g x = true

@[simp] theorem single {n : ℕ} (s : Finset (Fin n)) (p : Fin n) :
    line s {p} = true ↔ p ∈ s := by simp [line]

@[simp] theorem empty {n : ℕ} (s : Finset (Fin n)) : line s ∅ = false := by simp [line]

@[simp] theorem outside {n : ℕ} (s : Finset (Fin n)) : line s sᶜ = false := by simp [line]

theorem order {n : ℕ} {s t : Finset (Fin n)} (h : below (line s) (line t)) : s ⊆ t :=
  fun p hp => (single t p).mp (h {p} ((single s p).mpr hp))

def mark {n : ℕ} (s : Finset (Fin n)) (f : F n) : Prop :=
  (below f (line s) ∧ ∃ p r : Fin n, p ≠ r ∧ f {p} = true ∧ f {r} = true) ∨
  (below (line s) f ∧ f sᶜ = false) ∨
  f = fun x => !(line s x)

theorem pair_of_card {α : Type} [DecidableEq α] {s : Finset α} (h : 2 ≤ s.card) :
    ∃ p ∈ s, ∃ r ∈ s, p ≠ r := by
  have h' : 1 < s.card := by omega
  obtain ⟨p, hp, r, hr, hne⟩ := Finset.one_lt_card.mp h'
  exact ⟨p, hp, r, hr, hne⟩

theorem self_mark {n : ℕ} (s : Finset (Fin n)) : mark s (line s) :=
  .inr (.inl ⟨fun _ h => h, outside s⟩)

theorem no_input {n : ℕ} {s : Finset (Fin n)} (hs : 2 ≤ s.card) (v : Fin n) :
    ¬ mark s (point v) := by
  intro h
  obtain ⟨a, ha, b, hb, ne⟩ := pair_of_card hs
  rcases h with ⟨_,p,r,pr,hp,hr⟩ | ⟨h,_⟩ | h
  · simp [point] at hp hr
    exact pr (hp.symm.trans hr)
  · have h₁ := h {a} ((single s a).mpr ha)
    have h₂ := h {b} ((single s b).mpr hb)
    simp [point] at h₁ h₂
    exact ne (h₁.symm.trans h₂)
  · have e := congrFun h ∅
    simp [point] at e

theorem no_false {n : ℕ} {s : Finset (Fin n)} (hs : 2 ≤ s.card) :
    ¬ mark s (fun _ => false) := by
  intro h
  obtain ⟨a, ha, _⟩ := pair_of_card hs
  rcases h with ⟨_,p,r,_,hf,_⟩ | ⟨h,_⟩ | h
  · contradiction
  · exact Bool.noConfusion (h {a} ((single s a).mpr ha))
  · have e := congrFun h ∅
    simp at e

theorem mark_separate {n : ℕ} {s t : Finset (Fin n)} {f : F n}
    (meet : (s ∩ t).card = 1) (hs : 2 ≤ s.card) (ht : 2 ≤ t.card)
    (room : ∃ p : Fin n, p ∉ s ∧ p ∉ t) : ¬ (mark s f ∧ mark t f) := by
  obtain ⟨u, us, ut⟩ := room
  have hn₁ : ¬ s ⊆ t := by intro h; rw [Finset.inter_eq_left.mpr h] at meet; omega
  have hn₂ : ¬ t ⊆ s := by intro h; rw [Finset.inter_eq_right.mpr h] at meet; omega
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0 < (s ∩ t).card by omega)
  obtain ⟨zs,zt⟩ := Finset.mem_inter.mp hz
  intro ⟨a,b⟩
  rcases a with ⟨lo,p,r,pr,hp,hr⟩ | ⟨hi,off⟩ | neg
  · rcases b with ⟨lo',_⟩ | ⟨hi',_⟩ | neg'
    · have ps := (single s p).mp (lo {p} hp)
      have pt := (single t p).mp (lo' {p} hp)
      have rs := (single s r).mp (lo {r} hr)
      have rt := (single t r).mp (lo' {r} hr)
      have h := Finset.one_lt_card.mpr ⟨p,Finset.mem_inter.mpr ⟨ps,pt⟩,r,Finset.mem_inter.mpr ⟨rs,rt⟩,pr⟩
      omega
    · exact hn₂ (order (fun x h => lo x (hi' x h)))
    · have h := lo {u} (by simp [neg', line, ut])
      simp [line, us] at h
  · rcases b with ⟨lo',_⟩ | ⟨hi',_⟩ | neg'
    · exact hn₁ (order (fun x h => lo' x (hi x h)))
    · have h : ∃ p ∈ t, p ∉ s := by simpa [Finset.subset_iff, not_forall] using hn₂
      have v := hi' sᶜ (by simpa [line] using h)
      simp [off] at v
    · have h := hi {z} ((single s z).mpr zs)
      simp [neg',line,zt] at h
  · rcases b with ⟨lo',_⟩ | ⟨hi',_⟩ | neg'
    · have h := lo' {u} (by simp [neg,line,us])
      simp [line,ut] at h
    · have h := hi' {z} ((single t z).mpr zt)
      simp [neg,line,zs] at h
    · apply hn₁
      intro v hv
      have e := congrFun (neg.symm.trans neg') {v}
      simpa [line,hv] using e

end PEqualNP.Outside.L_meta_1042_aux

namespace PEqualNP.Outside.L_meta_1042_aux
open PEqualNP.CircuitLowerBounds

def read {n : ℕ} (w : List (F n)) (j : ℕ) : F n := w.getD j (fun _ => false)
def gateFun {n : ℕ} (w : List (F n)) (g : Gate) : F n :=
  fun x => g.op.eval (g.inputs.map fun i => read w i x)
def push {n : ℕ} (w : List (F n)) (g : Gate) := w ++ [gateFun w g]

theorem has_mem {n : ℕ} {s : Finset (Fin n)} (hs : 2 ≤ s.card) {w : List (F n)} {j : ℕ}
    (hm : mark s (read w j)) : read w j ∈ w := by
  by_cases hj : j < w.length
  · simp [read, List.getD_eq_getElem?_getD, hj, List.getElem_mem]
  · have h : read w j = fun _ => false := List.getD_eq_default _ _ (by omega)
    exact False.elim ((no_false hs) (h ▸ hm))

def sig {n : ℕ} (f : F n) := Finset.univ.filter fun p : Fin n => f {p} = true

theorem or_mark {n : ℕ} {s : Finset (Fin n)} (hs : 3 ≤ s.card) (f g : F n)
    (h : (fun x => f x || g x) = line s) : mark s f ∨ mark s g := by
  have he (x) : (f x || g x) = line s x := congrFun h x
  have lf : below f (line s) := fun x hx => by rw [← he, hx]; rfl
  have lg : below g (line s) := fun x hx => by rw [← he, hx]; simp
  have hu : s ⊆ sig f ∪ sig g := by
    intro p hp
    have v := (he {p}).trans ((single s p).mpr hp)
    simpa [sig] using v
  have hc := (Finset.card_le_card hu).trans (Finset.card_union_le _ _)
  have aux (a : F n) (ha : below a (line s)) (hc : 2 ≤ (sig a).card) : mark s a := by
    obtain ⟨p,hp,r,hr,pr⟩ := pair_of_card hc
    exact .inl ⟨ha,p,r,pr,by simpa [sig] using hp,by simpa [sig] using hr⟩
  by_cases hf : 2 ≤ (sig f).card
  · exact .inl (aux f lf hf)
  · exact .inr (aux g lg (by omega))

theorem and_mark {n : ℕ} {s : Finset (Fin n)} (f g : F n)
    (h : (fun x => f x && g x) = line s) : mark s f ∨ mark s g := by
  have he (x) : (f x && g x) = line s x := congrFun h x
  have lf : below (line s) f := fun x hx => (show f x = true ∧ g x = true by simpa using (he x).trans hx).1
  have lg : below (line s) g := fun x hx => (show f x = true ∧ g x = true by simpa using (he x).trans hx).2
  have hz := (he sᶜ).trans (outside s)
  cases hf : f sᶜ with
  | false => exact .inl (.inr (.inl ⟨lf,hf⟩))
  | true => exact .inr (.inr (.inl ⟨lg,by simpa [hf] using hz⟩))

theorem not_mark {n : ℕ} {s : Finset (Fin n)} (f : F n)
    (h : (fun x => !f x) = line s) : mark s f := by
  apply Or.inr; apply Or.inr
  funext x
  have e := congrFun h x
  change (!f x) = line s x at e
  rw [← e]; simp

theorem previous {n : ℕ} {s : Finset (Fin n)} (hs : 3 ≤ s.card) (w : List (F n)) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (h : gateFun w g = line s) : ∃ f ∈ w, mark s f := by
  have hm (j) (h' : mark s (read w j)) : ∃ f ∈ w, mark s f :=
    ⟨_,has_mem (by omega) h',h'⟩
  obtain ⟨p,hp,r,hr,pr⟩ := pair_of_card (s := s) (by omega)
  rcases g with ⟨op,ins⟩
  simp only at hop hlen
  match ins, hlen with
  | [], _ =>
    have z := congrFun h ∅
    have a := congrFun h {p}
    rcases hop with rfl | rfl | rfl <;> simp [gateFun,GateOp.eval,line,hp] at z a
  | [j], _ =>
    rcases hop with rfl | rfl | rfl
    · have e : read w j = line s := by funext x; simpa [gateFun,GateOp.eval] using congrFun h x
      exact hm j (e ▸ self_mark s)
    · have e : read w j = line s := by funext x; simpa [gateFun,GateOp.eval] using congrFun h x
      exact hm j (e ▸ self_mark s)
    · exact hm j (not_mark (read w j) (by funext x; simpa [gateFun,GateOp.eval] using congrFun h x))
  | [a,b], _ =>
    rcases hop with rfl | rfl | rfl
    · rcases and_mark (s := s) (read w a) (read w b) (by funext x; simpa [gateFun,GateOp.eval] using congrFun h x) with ha | hb
      · exact hm a ha
      · exact hm b hb
    · rcases or_mark hs (read w a) (read w b) (by funext x; simpa [gateFun,GateOp.eval] using congrFun h x) with ha | hb
      · exact hm a ha
      · exact hm b hb
    · exact hm a (not_mark (read w a) (by funext x; simpa [gateFun,GateOp.eval] using congrFun h x))
  | _ :: _ :: _ :: _, hlen => simp at hlen

def good {n : ℕ} (s : Finset (Fin n)) (w : List (F n)) : Prop :=
  line s ∈ w → ∃ f ∈ w, f ≠ line s ∧ mark s f

theorem grows {n : ℕ} {s : Finset (Fin n)} (hs : 3 ≤ s.card) {w : List (F n)}
    (hw : good s w) (g : Gate) (hg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    good s (push w g) := by
  intro he
  by_cases already : line s ∈ w
  · obtain ⟨f,hf,rest⟩ := hw already
    exact ⟨f,List.mem_append_left _ hf,rest⟩
  · have newGate : gateFun w g = line s := by simpa [push,already,eq_comm] using he
    obtain ⟨f,hf,hm⟩ := previous hs w g hg.1 hg.2 newGate
    exact ⟨f,List.mem_append_left _ hf,fun h => already (h ▸ hf),hm⟩

theorem foldGood {n : ℕ} {s : Finset (Fin n)} (hs : 3 ≤ s.card) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (w : List (F n)) (hw : good s w) : good s (gs.foldl push w) := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih => exact ih (fun t ht => hg t (by simp [ht])) _ (grows hs hw g (hg g (by simp)))

end PEqualNP.Outside.L_meta_1042_aux

namespace PEqualNP.Outside.L_meta_1042_aux
open PEqualNP.CircuitLowerBounds

theorem map_read {n : ℕ} (w : List (F n)) (x : Finset (Fin n)) (i : ℕ) :
    (w.map (fun f => f x)).getD i false = read w i x := by
  simp only [read,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

theorem eval_fold {n : ℕ} (gs : List Gate) (w : List (F n)) (x : Finset (Fin n)) :
    (gs.foldl push w).map (fun f => f x) =
    gs.foldl (fun bits g => bits ++ [g.op.eval (g.inputs.map (fun j => bits.getD j false))])
      (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons, ih, push, List.map_append, List.map_cons, List.map_nil, gateFun, map_read]

theorem circuit_read {n : ℕ} (gs : List Gate) (o : ℕ) (x : Finset (Fin n)) :
    read (gs.foldl push (List.ofFn (@point n))) o x =
    Circuit.eval ⟨gs,o⟩ (List.ofFn (fun p => decide (p ∈ x))) := by
  rw [← map_read,eval_fold]
  simp [Circuit.eval,Circuit.wires,List.map_ofFn,Function.comp_def,point]

theorem extendList {n : ℕ} (gs : List Gate) (w : List (F n)) :
    ∃ extra, gs.foldl push w = w ++ extra ∧ extra.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,by simp⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (push w g)
    refine ⟨gateFun w g :: t,?_,by simp [hl]⟩
    simpa [push,List.append_assoc] using ht

theorem lower {n m : ℕ} (S : Fin m → Finset (Fin n))
    (size : ∀ i, 3 ≤ (S i).card)
    (meet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (room : ∀ i j, i ≠ j → ∃ p, p ∉ S i ∧ p ∉ S j)
    (gs : List Gate) (o : Fin m → ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (correct : ∀ i (x : Fin n → Bool), Circuit.eval ⟨gs,o i⟩ (List.ofFn x) =
      decide (∃ p ∈ S i, x p = true)) : m * 2 ≤ gs.length := by
  classical
  let inputs := List.ofFn (@point n)
  let w := gs.foldl push inputs
  obtain ⟨extra,hext,hlen⟩ := extendList gs inputs
  have split : w = inputs ++ extra := hext
  have notRaw (i) {f : F n} (h : mark (S i) f) : f ∉ inputs := by
    intro hf
    obtain ⟨p,hp⟩ := List.mem_ofFn.mp hf
    rw [← hp] at h
    exact no_input (by have := size i; omega) p h
  have ready (i) : line (S i) ∈ w := by
    have eqn : read w (o i) = line (S i) := by
      funext x
      change read (gs.foldl push (List.ofFn (@point n))) (o i) x = _
      rw [circuit_read,correct]
      simp [line]
    rw [← eqn]
    exact has_mem (by have := size i; omega) (eqn ▸ self_mark (S i))
  have aux (i) : ∃ f ∈ extra, f ≠ line (S i) ∧ mark (S i) f := by
    have h0 : good (S i) inputs := fun h => False.elim ((notRaw i (self_mark _)) h)
    obtain ⟨f,hf,ne,markF⟩ := foldGood (size i) gs hg inputs h0 (ready i)
    change f ∈ w at hf
    rw [split,List.mem_append] at hf
    exact ⟨f,hf.resolve_left (notRaw i markF),ne,markF⟩
  choose witness hw hne hmark using aux
  have outs (i) : line (S i) ∈ extra := by
    have h := ready i
    rw [split,List.mem_append] at h
    exact h.resolve_left (notRaw i (self_mark _))
  let sel (z : Fin m × Bool) : ↥extra.toFinset :=
    if z.2 then ⟨witness z.1, by simpa using hw z.1⟩
    else ⟨line (S z.1), by simpa using outs z.1⟩
  have selMark (z) : mark (S z.1) (sel z).val := by
    rcases z with ⟨i, b⟩
    cases b <;> simp [sel,self_mark,hmark]
  have inj : Function.Injective sel := by
    rintro ⟨i,b⟩ ⟨j,c⟩ e
    have k := congrArg Subtype.val e
    have eqij : i = j := by
      by_contra ne
      exact mark_separate (meet i j ne) (by have := size i; omega) (by have := size j; omega)
        (room i j ne) ⟨selMark (i,b), k ▸ selMark (j,c)⟩
    subst j
    cases b <;> cases c <;> simp_all [sel,Ne.symm]
  calc
    m * 2 = Fintype.card (Fin m × Bool) := by simp
    _ ≤ Fintype.card ↥extra.toFinset := Fintype.card_le_of_injective sel inj
    _ = extra.toFinset.card := Fintype.card_coe _
    _ ≤ extra.length := List.toFinset_card_le _
    _ = gs.length := hlen

end PEqualNP.Outside.L_meta_1042_aux

theorem PEqualNP.Outside.L_meta_1042 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin 4 → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → (∀ (oa : Fin 4) (xa : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa, xa va = true)) → 8 ≤ gl.length := by
  intro _ gl ol gates _ computes
  let S : Fin 4 → Finset (Fin 6) := ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]
  exact PEqualNP.Outside.L_meta_1042_aux.lower S (by decide) (by decide) (by decide) gl ol gates computes
