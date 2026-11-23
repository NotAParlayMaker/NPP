import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import PEqualNP.Defs

-- Mythos 6 et Codex Betelgeuse

namespace PEqualNP.Outside.L_meta_717_aux

def value {G : Type} (ins : G → List ℕ) (ev : G → List Bool → Bool)
    (h : G) (w : List Bool) : Bool :=
  ev h ((ins h).map (fun i => w.getD i false))

def run {G : Type} (ins : G → List ℕ) (ev : G → List Bool → Bool)
    (gs : List G) (w : List Bool) : List Bool :=
  gs.foldl (fun w h => w ++ [value ins ev h w]) w

variable {G : Type} (ins : G → List ℕ) (ev : G → List Bool → Bool)

lemma run_nil (w : List Bool) : run ins ev [] w = w := rfl

lemma run_cons (h : G) (gs : List G) (w : List Bool) :
    run ins ev (h :: gs) w = run ins ev gs (w ++ [value ins ev h w]) := rfl

lemma run_append (a b : List G) (w : List Bool) :
    run ins ev (a ++ b) w = run ins ev b (run ins ev a w) :=
  List.foldl_append

lemma run_extension (gs : List G) (w : List Bool) :
    ∃ t, run ins ev gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons h gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [value ins ev h w])
    exact ⟨value ins ev h w :: t, by simpa [run_cons, List.append_assoc] using ht,
      by simp [hl]⟩

lemma run_length (gs : List G) (w : List Bool) :
    (run ins ev gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_extension ins ev gs w
  simp [ht, hl]

lemma run_getD (gs : List G) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run ins ev gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_extension ins ev gs w
  rw [ht]
  exact List.getD_append _ _ _ _ hi

def sameExcept (n : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, i ≠ n → a.getD i false = b.getD i false

lemma sameExcept_append (n : ℕ) (a b : List Bool) (c : Bool)
    (hab : sameExcept n a b) : sameExcept n (a ++ [c]) (b ++ [c]) := by
  refine ⟨by simp [hab.1], ?_⟩
  intro i hi
  have hl := hab.1
  by_cases h : i < a.length
  · rw [List.getD_append _ _ _ _ h,
      List.getD_append _ _ _ _ (by omega : i < b.length)]
    exact hab.2 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega : a.length ≤ i),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ i), hab.1]

lemma value_eq (h : G) (a b : List Bool) (n : ℕ)
    (hab : sameExcept n a b) (hn : n ∉ ins h) :
    value ins ev h a = value ins ev h b := by
  unfold value
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hab.2 i (by rintro rfl; exact hn hi)

lemma run_sameExcept (gs : List G) (a b : List Bool) (n : ℕ)
    (hab : sameExcept n a b) (hn : ∀ h ∈ gs, n ∉ ins h) :
    sameExcept n (run ins ev gs a) (run ins ev gs b) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons h gs ih =>
    rw [run_cons, run_cons]
    have he := value_eq ins ev h a b n hab (hn h (by simp))
    rw [he]
    apply ih _ _ (sameExcept_append n a b _ hab)
    intro h hh
    exact hn h (by simp [hh])

lemma input_sameExcept (y : List Bool) (a b : Bool) :
    sameExcept y.length (y ++ [a]) (y ++ [b]) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases h : i < y.length
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · have hgt : y.length < i := by omega
    rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

def redirect (n k i : ℕ) : ℕ :=
  if i < k then i else if i = k then n else i - 1

lemma redirect_getD (w s : List Bool) (n : ℕ) (hn : n < w.length) (i : ℕ) :
    ((w ++ [w.getD n false]) ++ s).getD i false =
      (w ++ s).getD (redirect n w.length i) false := by
  by_cases hi : i < w.length
  · simp only [redirect, ite_eq_left hi]
    rw [List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  · by_cases he : i = w.length
    · subst i
      simp only [redirect, lt_self_iff_false, ↓reduceIte]
      rw [List.getD_append _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (by omega),
        List.getD_append _ _ _ _ hn]
      simp
    · simp only [redirect, ite_eq_right hi, ite_eq_right he]
      rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      simp only [List.length_append, List.length_singleton]
      omega

lemma run_redirect (rename : (ℕ → ℕ) → G → G)
    (hi : ∀ f h, ins (rename f h) = (ins h).map f)
    (he : ∀ f h, ev (rename f h) = ev h)
    (gs : List G) (w s : List Bool) (n : ℕ) (hn : n < w.length) :
    ∃ t,
      run ins ev gs ((w ++ [w.getD n false]) ++ s) =
        (w ++ [w.getD n false]) ++ t ∧
      run ins ev (gs.map (rename (redirect n w.length))) (w ++ s) = w ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨s, rfl, rfl⟩
  | cons h gs ih =>
    have hv : value ins ev h ((w ++ [w.getD n false]) ++ s) =
        value ins ev (rename (redirect n w.length) h) (w ++ s) := by
      simp only [value, hi, he, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact redirect_getD w s n hn i
    simp only [List.map_cons, run_cons]
    rw [hv]
    simpa only [List.append_assoc] using
      ih (s ++ [value ins ev (rename (redirect n w.length) h) (w ++ s)])

lemma input_getD (y : List Bool) (b : Bool) :
    (y ++ [b]).getD y.length false = b := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma input_ofFn_getD {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    (List.ofFn y ++ [b]).getD n false = b := by
  simpa only [List.length_ofFn] using input_getD (List.ofFn y) b

lemma output_ne_fresh (n : ℕ) (g : (Fin n → Bool) → Bool)
    (gs : List G) (o : ℕ) (hg : ∃ y, g y = true)
    (hc : ∀ y b, (run ins ev gs (List.ofFn y ++ [b])).getD o false = xor b (g y)) :
    o ≠ n := by
  intro ho
  obtain ⟨y, hy⟩ := hg
  have hh := hc y false
  rw [ho, run_getD ins ev gs _ n (by simp), input_ofFn_getD] at hh
  simp [hy] at hh

lemma copy_value (n : ℕ) (g : (Fin n → Bool) → Bool)
    (p s : List G) (h : G) (o : ℕ)
    (ho : o ≠ n) (hp : ∀ a ∈ p, n ∉ ins a) (hs : ∀ a ∈ s, n ∉ ins a)
    (ha : ∃ a : Bool, ∀ w : List Bool, w.getD n false = a → value ins ev h w = a)
    (hc : ∀ y b, (run ins ev (p ++ h :: s) (List.ofFn y ++ [b])).getD o false =
      xor b (g y)) :
    ∀ (y : Fin n → Bool) (b : Bool),
      value ins ev h (run ins ev p (List.ofFn y ++ [b])) = b := by
  intro y
  have hw (b : Bool) :
      (run ins ev p (List.ofFn y ++ [b])).getD n false = b := by
    rw [run_getD ins ev p _ n (by simp), input_ofFn_getD]
  have hab : sameExcept n (run ins ev p (List.ofFn y ++ [false]))
      (run ins ev p (List.ofFn y ++ [true])) := by
    apply run_sameExcept ins ev _ _ _ _ _ hp
    simpa using input_sameExcept (List.ofFn y) false true
  have hd : value ins ev h (run ins ev p (List.ofFn y ++ [false])) ≠
      value ins ev h (run ins ev p (List.ofFn y ++ [true])) := by
    intro hh
    have hh' := sameExcept_append n _ _
      (value ins ev h (run ins ev p (List.ofFn y ++ [true]))) hab
    rw [← hh] at hh'
    have hz := (run_sameExcept ins ev s _ _ n hh' hs).2 o ho
    have hf := hc y false
    have ht := hc y true
    simp only [run_append, run_cons] at hf ht
    rw [hh] at hf
    rw [hh] at hz
    rw [hf, ht] at hz
    cases g y <;> simp at hz
  obtain ⟨a, ha⟩ := ha
  have hanchor := ha (run ins ev p (List.ofFn y ++ [a])) (hw a)
  have hpair :
      value ins ev h (run ins ev p (List.ofFn y ++ [false])) = false ∧
      value ins ev h (run ins ev p (List.ofFn y ++ [true])) = true := by
    cases a <;>
      cases h0 : value ins ev h (run ins ev p (List.ofFn y ++ [false])) <;>
      cases h1 : value ins ev h (run ins ev p (List.ofFn y ++ [true])) <;>
      simp_all
  intro b
  cases b
  · exact hpair.1
  · exact hpair.2

lemma shorten (rename : (ℕ → ℕ) → G → G)
    (hi : ∀ f h, ins (rename f h) = (ins h).map f)
    (he : ∀ f h, ev (rename f h) = ev h)
    (P : G → Prop) (hP : ∀ f h, P h → P (rename f h))
    (n : ℕ) (g : (Fin n → Bool) → Bool)
    (p s : List G) (h : G) (o : ℕ)
    (hps : ∀ a ∈ p ++ h :: s, P a)
    (hp : ∀ a ∈ p, n ∉ ins a) (hs : ∀ a ∈ s, n ∉ ins a)
    (ha : ∃ a : Bool, ∀ w : List Bool, w.getD n false = a → value ins ev h w = a)
    (hg : ∃ y, g y = true)
    (hc : ∀ y b, (run ins ev (p ++ h :: s) (List.ofFn y ++ [b])).getD o false =
      xor b (g y)) :
    ∃ (gs : List G) (o' : ℕ),
      (∀ a ∈ gs, P a) ∧ gs.length + 1 = (p ++ h :: s).length ∧
      ∀ y b, (run ins ev gs (List.ofFn y ++ [b])).getD o' false = xor b (g y) := by
  let k := n + 1 + p.length
  let f := redirect n k
  refine ⟨p ++ s.map (rename f), f o, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hps a (List.mem_append_left _ ha)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hP f b (hps b (by simp [hb]))
  · simp [Nat.add_assoc]
  · intro y b
    have ho := output_ne_fresh ins ev n g (p ++ h :: s) o hg hc
    have hv := copy_value ins ev n g p s h o ho hp hs ha hc y b
    let w := run ins ev p (List.ofFn y ++ [b])
    have hwlen : w.length = k := by simp [w, run_length, k]
    have hn : n < w.length := by rw [hwlen]; omega
    have hwb : w.getD n false = b := by
      dsimp [w]
      rw [run_getD ins ev p _ n (by simp), input_ofFn_getD]
    obtain ⟨t, ht, ht'⟩ := run_redirect ins ev rename hi he s w [] n hn
    simp only [List.append_nil] at ht ht'
    have hr := redirect_getD w t n hn o
    rw [← ht, ← ht'] at hr
    rw [hwb] at hr
    have hc' := hc y b
    simp only [run_append, run_cons] at hc'
    rw [hv] at hc'
    rw [run_append]
    change (run ins ev (s.map (rename f)) w).getD (f o) false = _
    simpa only [f, hwlen] using hr.symm.trans hc'

lemma split_at {gs : List G} {j : ℕ} {h : G} (hj : gs[j]? = some h) :
    ∃ p s, gs = p ++ h :: s ∧ p.length = j := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons a gs ih =>
    cases j with
    | zero =>
      have hh : a = h := by simpa using hj
      subst a
      exact ⟨[], gs, rfl, rfl⟩
    | succ j =>
      obtain ⟨p, s, hp, hl⟩ := ih (by simpa using hj)
      exact ⟨a :: p, s, by simp [hp], by simp [hl]⟩

lemma unique_split (n : ℕ) (p s : List G) (h : G)
    (hu : ∀ j a, (p ++ h :: s)[j]? = some a → n ∈ ins a → j = p.length) :
    (∀ a ∈ p, n ∉ ins a) ∧ (∀ a ∈ s, n ∉ ins a) := by
  constructor
  · intro a ha hn
    obtain ⟨i, hi, hai⟩ := List.mem_iff_getElem.mp ha
    have hx : (p ++ h :: s)[i]? = some a := by
      rw [List.getElem?_append_left hi]
      exact List.getElem?_eq_some_iff.mpr ⟨hi, hai⟩
    have hh := hu i a hx hn
    omega
  · intro a ha hn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hx : (p ++ h :: s)[p.length + (i + 1)]? = some a := by
      rw [List.getElem?_append_right (by omega)]
      simpa using hi
    have hh := hu _ a hx hn
    omega

lemma nonconstant_true {n : ℕ} (g : (Fin n → Bool) → Bool)
    (hg : ∃ y y', g y ≠ g y') : ∃ y, g y = true := by
  obtain ⟨y, y', hg⟩ := hg
  cases hy : g y <;> cases hy' : g y' <;> simp_all
  · exact ⟨y', hy'⟩
  · exact ⟨y, hy⟩

lemma no_unique (rename : (ℕ → ℕ) → G → G)
    (hi : ∀ f h, ins (rename f h) = (ins h).map f)
    (he : ∀ f h, ev (rename f h) = ev h)
    (P : G → Prop) (hP : ∀ f h, P h → P (rename f h))
    (n : ℕ) (g : (Fin n → Bool) → Bool) (gs : List G) (o : ℕ)
    (hgs : ∀ a ∈ gs, P a) (hg : ∃ y y', g y ≠ g y')
    (hc : ∀ x : Fin (n + 1) → Bool,
      (run ins ev gs (List.ofFn x)).getD o false =
        xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)))
    (hm : ∀ (gs' : List G) (o' : ℕ), (∀ a ∈ gs', P a) →
      (∀ x : Fin (n + 1) → Bool,
        (run ins ev gs' (List.ofFn x)).getD o' false =
          xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) →
      gs.length ≤ gs'.length)
    (j : ℕ) (h : G) (hj : gs[j]? = some h)
    (ha : ∃ a : Bool, ∀ w : List Bool, w.getD n false = a → value ins ev h w = a)
    (hu : ∀ j' h', gs[j']? = some h' → n ∈ ins h' → j' = j) : False := by
  obtain ⟨p, s, rfl, rfl⟩ := split_at hj
  obtain ⟨hp, hs⟩ := unique_split ins n p s h hu
  have hcs : ∀ y b,
      (run ins ev (p ++ h :: s) (List.ofFn y ++ [b])).getD o false = xor b (g y) := by
    intro y b
    have hx := hc (Fin.snoc y b)
    simpa only [List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last] using hx
  obtain ⟨gs', o', hgs', hl, hc'⟩ :=
    shorten ins ev rename hi he P hP n g p s h o hgs hp hs ha (nonconstant_true g hg) hcs
  have hle := hm gs' o' hgs' (by
    intro x
    rw [List.ofFn_succ_last]
    exact hc' (fun i : Fin n => x i.castSucc) (x (Fin.last n)))
  omega

lemma all_anchor (l : List ℕ) (n : ℕ) (hn : n ∈ l) (w : List Bool)
    (hw : w.getD n false = false) : (l.map (fun i => w.getD i false)).all id = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have he := List.all_eq_true.mp hh false
    (List.mem_map.mpr ⟨n, hn, hw⟩)
  simp at he

lemma any_anchor (l : List ℕ) (n : ℕ) (hn : n ∈ l) (w : List Bool)
    (hw : w.getD n false = true) : (l.map (fun i => w.getD i false)).any id = true := by
  apply List.any_eq_true.mpr
  exact ⟨true, List.mem_map.mpr ⟨n, hn, hw⟩, rfl⟩

end PEqualNP.Outside.L_meta_717_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_717_aux

theorem PEqualNP.Outside.L_meta_717 :
∀ (n : ℕ) (g : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ y y' : Fin n → Bool, g y ≠ g y') → PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' → (∀ x : Fin (n + 1) → Bool, C'.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → C.size ≤ C'.size) → ¬ ∃ (j : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some h ∧ (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n ∈ h.inputs ∧ ∀ (j' : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[j']? = some h' → n ∈ h'.inputs → j' = j := by
  intro n g C hg hC hc hm hex
  obtain ⟨j, h, hj, hop, hread, huniq⟩ := hex
  let operation (q : Gate) := q.op.eval
  let rename (f : ℕ → ℕ) (q : Gate) : Gate := ⟨q.op, q.inputs.map f⟩
  let allowed (q : Gate) : Prop := q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ q.inputs.length ≤ 2
  have hf (f : ℕ → ℕ) (q : Gate) (hq : allowed q) : allowed (rename f q) :=
    ⟨hq.1, by simpa [rename] using hq.2⟩
  apply no_unique Gate.inputs operation rename (fun _ _ => rfl) (fun _ _ => rfl) allowed hf n g C.gates C.output hC hg hc (fun gs out hgs hfun => hm ⟨gs, out⟩ hgs hfun) j h hj _ huniq
  rcases hop with hand | hor
  · refine ⟨false, ?_⟩
    intro w hw
    simpa only [value, operation, hand, GateOp.eval] using all_anchor h.inputs n hread w hw
  · refine ⟨true, ?_⟩
    intro w hw
    simpa only [value, operation, hor, GateOp.eval] using any_anchor h.inputs n hread w hw
