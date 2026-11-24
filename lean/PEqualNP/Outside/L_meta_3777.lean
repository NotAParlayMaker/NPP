import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3777

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

def back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j g, gs[j]? = some g → ∀ i ∈ g.inputs, i < n + j

def ao (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def bad (g : Gate) : Prop :=
  g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0

def value (w : List Bool) : Bool ⊕ ℕ → Bool := Sum.elim id (fun i => w.getD i false)

def bounded (n : ℕ) : Bool ⊕ ℕ → Prop := Sum.elim (fun _ => True) (· < n)

theorem bounded_mono {n m : ℕ} (h : n ≤ m) (t : Bool ⊕ ℕ) (ht : bounded n t) : bounded m t := by
  cases t with
  | inl b => exact trivial
  | inr i => exact Nat.lt_of_lt_of_le ht h

theorem run_len (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step x g)).length = _
    rw [ih]
    simp [step]
    omega

theorem run_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step x g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem back_split {n : ℕ} {a b : List Gate} :
    back n (a ++ b) ↔ back n a ∧ back (n + a.length) b := by
  constructor
  · intro h
    constructor
    · intro j g hj i hi
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
      apply h j g _ i hi
      rw [List.getElem?_append_left hlt, hj]
    · intro j g hj i hi
      have he : (a ++ b)[a.length+j]? = some g := by rw [List.getElem?_append_right (by omega), show a.length+j-a.length=j by omega, hj]
      have := h (a.length+j) g he i hi
      omega
  · rintro ⟨ha, hb⟩ j g hj i hi
    by_cases hlt : j < a.length
    · rw [List.getElem?_append_left hlt] at hj
      exact ha j g hj i hi
    · rw [List.getElem?_append_right (by omega)] at hj
      have := hb (j-a.length) g hj i hi
      omega

theorem back_one {n : ℕ} {g : Gate} (h : ∀ i ∈ g.inputs, i < n) : back n [g] := by
  intro j d hj i hi
  cases j with
  | zero => simp at hj; subst d; simpa using h i hi
  | succ j => simp at hj

theorem emit (n : ℕ) (g : Gate) (tg : ℕ → Bool ⊕ ℕ)
    (ho : g.op = GateOp.and ∨ g.op = GateOp.or) (hl : g.inputs.length ≤ 2)
    (ht : ∀ i ∈ g.inputs, bounded n (tg i)) :
    ∃ (tail : List Gate) (t : Bool ⊕ ℕ),
      ao tail ∧ back n tail ∧ tail.length ≤ 1 ∧ (bad g → tail = []) ∧
      bounded (n + tail.length) t ∧
      ∀ w : List Bool, w.length = n →
        value (run tail w) t = g.op.eval (g.inputs.map fun i => value w (tg i)) := by
  have empty (t : Bool ⊕ ℕ) (hb : bounded n t)
      (he : ∀ w : List Bool, w.length = n → value w t =
        g.op.eval (g.inputs.map fun i => value w (tg i))) :
      ∃ (tail : List Gate) (t : Bool ⊕ ℕ),
        ao tail ∧ back n tail ∧ tail.length ≤ 1 ∧ (bad g → tail = []) ∧
        bounded (n + tail.length) t ∧
        ∀ w : List Bool, w.length = n →
          value (run tail w) t = g.op.eval (g.inputs.map fun i => value w (tg i)) :=
    ⟨[], t, by simp [ao], by simp [back], by simp, fun _ => rfl, by simpa using hb, he⟩
  obtain ⟨op, inputs⟩ := g
  rcases inputs with _ | ⟨a, inputs⟩
  · rcases ho with rfl | rfl
    · exact empty (.inl true) trivial (fun _ _ => rfl)
    · exact empty (.inl false) trivial (fun _ _ => rfl)
  rcases inputs with _ | ⟨b, inputs⟩
  · apply empty (tg a) (ht a (by simp))
    intro w _
    rcases ho with rfl | rfl <;> simp [GateOp.eval]
  have hab : inputs = [] := by simpa using hl
  subst inputs
  by_cases he : a = b
  · subst b
    apply empty (tg a) (ht a (by simp))
    intro w _
    rcases ho with rfl | rfl <;> simp [GateOp.eval]
  have ha := ht a (by simp)
  have hb := ht b (by simp)
  cases hta : tg a with
  | inl c =>
    rcases ho with rfl | rfl <;> cases c
    · exact empty (.inl false) trivial (by intros; simp [hta, value, GateOp.eval])
    · exact empty (tg b) hb (by intros; simp [hta, value, GateOp.eval])
    · exact empty (tg b) hb (by intros; simp [hta, value, GateOp.eval])
    · exact empty (.inl true) trivial (by intros; simp [hta, value, GateOp.eval])
  | inr u =>
    cases htb : tg b with
    | inl c =>
      rcases ho with rfl | rfl <;> cases c
      · exact empty (.inl false) trivial (by intros; simp [htb, value, GateOp.eval])
      · exact empty (tg a) ha (by intros; simp [htb, value, GateOp.eval])
      · exact empty (tg a) ha (by intros; simp [htb, value, GateOp.eval])
      · exact empty (.inl true) trivial (by intros; simp [htb, value, GateOp.eval])
    | inr v =>
      have hu : u < n := by simpa [hta, bounded] using ha
      have hv : v < n := by simpa [htb, bounded] using hb
      refine ⟨[⟨op, [u,v]⟩], .inr n, ?_, back_one ?_, by simp, ?_, ?_, ?_⟩
      · simpa [ao] using ho
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
      · simp [bad, he]
      · simp [bounded]
      · intro w hw
        change ((w ++ [_]).getD n false) = _
        rw [List.getD_append_right _ _ _ _ hw.le, hw, Nat.sub_self]
        simp [hta, htb, value]

theorem shrink (n : ℕ) (gs : List Gate) (ho : ao gs) (hb : back n gs) :
    ∃ (ds : List Gate) (tg : ℕ → Bool ⊕ ℕ),
      ao ds ∧ back n ds ∧ ds.length ≤ gs.length ∧
      ((∃ g ∈ gs, bad g) → ds.length < gs.length) ∧
      (∀ i < n + gs.length, bounded (n + ds.length) (tg i)) ∧
      ∀ (x : List Bool), x.length = n → ∀ i < n + gs.length,
        value (run ds x) (tg i) = (run gs x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], Sum.inr, ho, hb, le_rfl, ?_, ?_, ?_⟩
    · simp
    · exact fun _ hi => hi
    · intros; rfl
  | append_singleton gs g ih =>
    have hog := ho g (by simp)
    obtain ⟨hbg, hblast⟩ := back_split.mp hb
    obtain ⟨ds, tg, hao, hback, hle, hstrict, hbound, heval⟩ :=
      ih (fun d hd => ho d (List.mem_append_left _ hd)) hbg
    have hreads : ∀ i ∈ g.inputs, i < n + gs.length := by
      intro i hi
      simpa using hblast 0 g (by simp) i hi
    obtain ⟨tail, t, htailao, htailback, htaillen, hbad, htb, htv⟩ :=
      emit (n + ds.length) g tg hog.1 hog.2 (fun i hi => hbound i (hreads i hi))
    let k := n + gs.length
    let map := Function.update tg k t
    refine ⟨ds ++ tail, map, ?_, back_split.mpr ⟨hback, htailback⟩, ?_, ?_, ?_, ?_⟩
    · intro d hd
      exact (List.mem_append.mp hd).elim (hao d) (htailao d)
    · simp only [List.length_append, List.length_singleton]; omega
    · rintro ⟨d, hd, hdBad⟩
      rcases List.mem_append.mp hd with hd | hd
      · have hs := hstrict ⟨d, hd, hdBad⟩
        simp only [List.length_append, List.length_singleton]; omega
      · have he : d = g := List.mem_singleton.mp hd
        subst d
        rw [hbad hdBad]
        simp only [List.length_append, List.length_singleton, List.length_nil]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hh : i = k
      · subst i
        simpa [map, Nat.add_assoc] using htb
      · have hii : i < n + gs.length := by dsimp [k] at hh; omega
        simpa [map, hh] using bounded_mono (show n + ds.length ≤ n + (ds.length + tail.length) by omega) (tg i) (hbound i hii)
    · intro x hx i hi
      simp only [List.length_append, List.length_singleton] at hi
      have hdl : (run ds x).length = n + ds.length := by rw [run_len, hx]
      have hgl : (run gs x).length = k := by rw [run_len, hx]
      have hrun (a b : List Gate) : run (a ++ b) x = run b (run a x) := List.foldl_append
      rw [hrun, hrun]
      change value (run tail (run ds x)) (map i) = (step (run gs x) g).getD i false
      by_cases hh : i = k
      · subst i
        simp only [map, Function.update_self]
        rw [htv _ hdl]
        change _ = ((run gs x) ++ [_]).getD k false
        rw [List.getD_append_right _ _ _ _ hgl.le, hgl, Nat.sub_self]
        change g.op.eval (g.inputs.map fun j => value (run ds x) (tg j)) = _
        congr 1
        exact List.map_congr_left (fun j hj => heval x hx j (hreads j hj))
      · have hii : i < n + gs.length := by dsimp [k] at hh; omega
        rw [show map i = tg i by simp [map, hh], step, List.getD_append _ _ _ _ (by rw [hgl]; exact hii)]
        have htag := hbound i hii
        cases ht : tg i with
        | inl b => simpa [ht, value] using heval x hx i hii
        | inr j =>
          have hj : j < (run ds x).length := by rw [hdl]; simpa [ht, bounded] using htag
          simp only [value, Sum.elim_inr]
          rw [run_prefix tail _ _ hj]
          simpa [ht, value] using heval x hx i hii

end PEqualNP.Outside.L_meta_3777


theorem PEqualNP.Outside.L_meta_3777 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → x4.size < (64 : ℕ) → (∃ x7 ∈ x4.gates, x7.inputs.length < (2 : ℕ) ∨ x7.inputs.getD (0 : ℕ) (0 : ℕ) = x7.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 ∧ x8.size < x4.size := by
  intro S data good C hC _ hbad
  rcases C with ⟨gs, out⟩
  have hao : PEqualNP.Outside.L_meta_3777.ao gs := by
    intro g hg
    simpa only [PEqualNP.MetaComplexity.Monotone2, Set.mem_insert_iff, Set.mem_singleton_iff] using hC.1 g hg
  have hback : PEqualNP.Outside.L_meta_3777.back 26 gs := by
    intro j g hj i hi
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
    have he : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, out⟩ j = g := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj, Option.getD_some]
    apply hC.2.1 j hlt i
    rwa [he]
  have hshrink : ∃ g ∈ gs, PEqualNP.Outside.L_meta_3777.bad g := hbad
  obtain ⟨ds, tg, hao', hback', _, hsize, hbound, heval⟩ :=
    PEqualNP.Outside.L_meta_3777.shrink 26 gs hao hback
  have hlt : ds.length < gs.length := hsize hshrink
  let pos : List Bool := (List.ofFn fun p : Fin 13 => decide (p = 0)) ++
    List.ofFn fun l : Fin 13 => decide (l = 0)
  let Q : Finset (Fin 13) := {0,2,3,4}
  let neg : List Bool := (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
    List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ S)
  have hp : data true pos := by
    change ∃ p l : Fin 13, p - l ∈ S ∧ pos = _
    exact ⟨0, 0, by decide, rfl⟩
  have hn : data false neg := by
    change ∃ P : Finset (Fin 13), P.card = 4 ∧
      (∀ l : Fin 13, (P.filter fun p => p-l ∈ S).card ≤ 2) ∧ neg = _
    exact ⟨Q, by decide, by decide, rfl⟩
  have hpos : (PEqualNP.Outside.L_meta_3777.run gs pos).getD out false = true := hC.2.2 true pos hp
  have hneg : (PEqualNP.Outside.L_meta_3777.run gs neg).getD out false = false := hC.2.2 false neg hn
  have hout : out < 26 + gs.length := by
    by_contra! h
    have he : (PEqualNP.Outside.L_meta_3777.run gs pos).getD out false = false := by
      apply List.getD_eq_default
      rw [PEqualNP.Outside.L_meta_3777.run_len, show pos.length = 26 by simp [pos]]
      exact h
    rw [he] at hpos
    contradiction
  cases htag : tg out with
  | inl b =>
    have h₁ : b = true := by
      have he := heval pos (by simp [pos]) out hout
      rw [htag] at he
      exact he.trans hpos
    have h₂ : b = false := by
      have he := heval neg (by simp [neg]) out hout
      rw [htag] at he
      exact he.trans hneg
    rw [h₁] at h₂
    contradiction
  | inr j =>
    refine ⟨⟨ds, j⟩, ⟨?_, ?_, ?_⟩, hlt⟩
    · intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hao' g hg
    · intro i hi w hw
      have he : ds[i]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨ds,j⟩ i) := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hback' i _ he w hw
    · intro b x hx
      have hlen : x.length = 26 := by
        cases b
        · change (∃ P : Finset (Fin 13), P.card = 4 ∧ _ ∧ x = _) at hx
          obtain ⟨P, _, _, rfl⟩ := hx
          simp
        · change (∃ p l : Fin 13, _ ∧ x = _) at hx
          obtain ⟨p, l, _, rfl⟩ := hx
          simp
      have he := heval x hlen out hout
      simp only [htag, PEqualNP.Outside.L_meta_3777.value, Sum.elim_inr] at he
      change (PEqualNP.Outside.L_meta_3777.run ds x).getD j false = b
      rw [he]
      exact hC.2.2 b x hx
