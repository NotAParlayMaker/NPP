import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace Meta278

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

def run (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn x)

def wire (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (run gs x).getD i false

def step (g : Gate) (f : ℕ → Bool) : Bool :=
  g.op.eval (g.inputs.map f)

def ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem run_snoc (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    run (gs ++ [g]) x = run gs x ++ [step g (wire gs x)] := by
  simp [run, Circuit.wires, List.foldl_append, step]
  rfl

theorem run_len (gs : List Gate) (x : Fin n → Bool) :
    (run gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run, Circuit.wires]
  | append_singleton gs g ih => simp [run_snoc, ih, Nat.add_assoc]

theorem wire_old (gs : List Gate) (g : Gate) (x : Fin n → Bool)
    {i : ℕ} (h : i ≠ n + gs.length) : wire (gs ++ [g]) x i = wire gs x i := by
  simp only [wire, run_snoc]
  by_cases hi : i < (run gs x).length
  · exact List.getD_append _ _ _ _ hi
  · have hl := run_len gs x
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem wire_new (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wire (gs ++ [g]) x (n + gs.length) = step g (wire gs x) := by
  rw [← run_len gs x]
  simp [wire, run_snoc]

theorem step_mono {g : Gate} (hg : ok g) {f f' : ℕ → Bool}
    (h : ∀ i ∈ g.inputs, f i = true → f' i = true) :
    step g f = true → step g f' = true := by
  rcases hg.1 with hop | hop
  · simpa [step, hop, GateOp.eval] using
      (show (∀ i ∈ g.inputs, f i = true) → ∀ i ∈ g.inputs, f' i = true from
        fun hf i hi => h i hi (hf i hi))
  · simpa [step, hop, GateOp.eval] using
      (show (∃ i ∈ g.inputs, f i = true) → ∃ i ∈ g.inputs, f' i = true from
        fun ⟨i, hi, hf⟩ => ⟨i, hi, h i hi hf⟩)

theorem wire_nil (x : Fin n → Bool) (i : ℕ) :
    wire [] x i = if h : i < n then x ⟨i,h⟩ else false := by
  by_cases h : i < n
  · simp [wire, run, Circuit.wires, List.getD_eq_getElem?_getD, h]
  · simp [wire, run, Circuit.wires, List.getD_eq_getElem?_getD, h]

theorem wire_mono (gs : List Gate) (hg : ∀ g ∈ gs, ok g)
    {x y : Fin n → Bool} (h : ∀ p, x p = true → y p = true) (i : ℕ) :
    wire gs x i = true → wire gs y i = true := by
  induction gs using List.reverseRecOn generalizing i with
  | nil => simp only [wire_nil]; split <;> simp_all
  | append_singleton gs g ih =>
    by_cases hi : i = n + gs.length
    · subst i
      rw [wire_new, wire_new]
      apply step_mono (hg g (by simp))
      intro j _
      exact ih (fun a ha => hg a (by simp [ha])) j
    · rw [wire_old _ _ _ hi, wire_old _ _ _ hi]
      exact ih (fun a ha => hg a (by simp [ha])) i

def point (p : Fin n) (q : Fin n) : Bool := decide (q = p)

def bits (T : Finset (Fin n)) (q : Fin n) : Bool := decide (q ∈ T)

-- Singleton inputs that make a given wire true.
def support (gs : List Gate) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => wire gs (point p) i = true

abbrev good (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  support gs i ⊆ S ∧ 2 ≤ (support (n := n) gs i).card

def count (S : Finset (Fin n)) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter (fun j => good S gs (n+j))).card

theorem count_snoc (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    count S (gs ++ [g]) =
      count S gs + if good S (gs ++ [g]) (n + gs.length) then 1 else 0 := by
  classical
  have hEq : (Finset.range gs.length).filter (fun j => good S (gs ++ [g]) (n+j)) =
      (Finset.range gs.length).filter (fun j => good S gs (n+j)) := by
    apply Finset.filter_congr
    intro j hj
    have hne : n+j ≠ n+gs.length := by have := Finset.mem_range.mp hj; omega
    have hs : support (n := n) (gs ++ [g]) (n+j) = support gs (n+j) := by
      simp [support, wire_old gs g _ hne]
    simp [good, hs]
  unfold count
  simp only [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  split <;> simp_all

-- On the wires in F, the single input p is simulated by T whenever p lies outside A.
def covers (S A T : Finset (Fin n)) (gs : List Gate) (F : Finset ℕ) : Prop :=
  ∀ p ∈ S, p ∉ A → ∀ i ∈ F,
    wire gs (point p) i = true → wire gs (bits T) i = true

-- Each wire in the frontier costs at most one exception and one outside input.
-- Expanding a counted gate into two input wires pays for the increase in the frontier.
theorem cover (S : Finset (Fin n)) (gs : List Gate) (hg : ∀ g ∈ gs, ok g) (F : Finset ℕ) :
    ∃ A T : Finset (Fin n), A.card ≤ F.card + count S gs ∧ T.card ≤ F.card + count S gs ∧
      (∀ q ∈ T, q ∉ S) ∧ covers S A T gs F := by
  classical
  induction gs using List.reverseRecOn generalizing F with
  | nil =>
    let A := Finset.univ.filter (fun p : Fin n => p.val ∈ F)
    have hA : A.card ≤ F.card := by
      apply Finset.card_le_card_of_injOn Fin.val
      · intro p hp
        simpa [A] using hp
      · exact fun _ _ _ _ h => Fin.ext h
    refine ⟨A, ∅, by simp [count]; exact hA, by simp, by simp, ?_⟩
    intro p hp hn i hi h
    rw [wire_nil] at h
    split at h
    next hlt =>
      have heq : (⟨i,hlt⟩ : Fin n) = p := by simpa [point] using h
      exact False.elim (hn (by simpa [A, ← heq] using hi))
    next => contradiction
  | append_singleton gs g ih =>
    let m := n + gs.length
    let last := gs ++ [g]
    have hpre : ∀ a ∈ gs, ok a := fun a ha => hg a (by simp [ha])
    have hgate : ok g := hg g (by simp)
    have hcount := count_snoc S gs g
    have hle : count S gs ≤ count S last := by dsimp [last]; rw [hcount]; omega
    by_cases hm : m ∈ F
    · let R := F.erase m
      have hR : R.card + 1 = F.card := Finset.card_erase_add_one hm
      have oldmem {i : ℕ} (hi : i ∈ F) (hne : i ≠ m) : i ∈ R := by simp [R, hi, hne]
      by_cases hgood : good S last m
      · -- Trace both inputs of the counted gate back to the earlier wires.
        let D := R ∪ g.inputs.toFinset
        have hD : D.card ≤ R.card + 2 := by
          calc
            D.card ≤ R.card + g.inputs.toFinset.card := Finset.card_union_le _ _
            _ ≤ R.card + 2 := by have := List.toFinset_card_le g.inputs; have := hgate.2; omega
        obtain ⟨A,T,ha,ht,hd,hc⟩ := ih hpre D
        have he : count S last = count S gs + 1 := by
          change count S (gs ++ [g]) = _
          rw [hcount, ite_eq_left hgood]
        have hb : D.card + count S gs ≤ F.card + count S last := by omega
        refine ⟨A,T,ha.trans hb,ht.trans hb,hd,?_⟩
        intro p hp hn i hi hw
        by_cases eq : i = m
        · subst i
          rw [wire_new] at hw ⊢
          apply step_mono hgate _ hw
          intro j hj
          exact hc p hp hn j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
        · rw [wire_old _ _ _ eq] at hw ⊢
          exact hc p hp hn i (Finset.mem_union_left _ (oldmem hi eq)) hw
      · obtain ⟨A,T,ha,ht,hd,hc⟩ := ih hpre R
        by_cases hs : support last m ⊆ S
        · -- This wire has at most one singleton in its support.
          let B := support (n := n) last m
          have hb : B.card ≤ 1 := by
            have hlt : ¬ 2 ≤ B.card := fun h => hgood ⟨hs,h⟩
            omega
          refine ⟨A ∪ B,T,?_,by omega,hd,?_⟩
          · have := Finset.card_union_le A B; omega
          · intro p hp hn i hi hw
            have hn' := Finset.notMem_union.mp hn
            by_cases eq : i = m
            · subst i
              exact False.elim (hn'.2 (by simpa [B, support, last] using hw))
            · rw [wire_old _ _ _ eq] at hw ⊢
              exact hc p hp hn'.1 i (oldmem hi eq) hw
        · -- One outside input makes this wire true, independently of p.
          obtain ⟨q,hq,hout⟩ := Finset.not_subset.mp hs
          let U := insert q T
          have hu : U.card ≤ T.card + 1 := Finset.card_insert_le _ _
          refine ⟨A,U,by omega,by omega,?_,?_⟩
          · intro r hr
            rcases Finset.mem_insert.mp hr with h | h
            · simpa [h] using hout
            · exact hd r h
          · intro p hp hn i hi hw
            by_cases eq : i = m
            · subst i
              have hq' : wire last (point q) m = true := (Finset.mem_filter.mp hq).2
              apply wire_mono last hg _ m hq'
              intro r hr
              simpa [point, bits, U] using (show r = q ∨ r ∈ T from Or.inl (by simpa [point] using hr))
            · rw [wire_old _ _ _ eq] at hw ⊢
              apply wire_mono gs hpre _ i (hc p hp hn i (oldmem hi eq) hw)
              intro r hr
              simp only [bits, decide_eq_true_eq] at hr ⊢
              exact Finset.mem_insert_of_mem hr
    · obtain ⟨A,T,ha,ht,hd,hc⟩ := ih hpre F
      refine ⟨A,T,by omega,by omega,hd,?_⟩
      intro p hp hn i hi hw
      have hne : i ≠ m := fun h => hm (h ▸ hi)
      rw [wire_old _ _ _ hne] at hw ⊢
      exact hc p hp hn i hi hw

end Meta278

open Meta278

theorem PEqualNP.Outside.L_meta_278 : ∀ (n k c o : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true ↔ p ∈ S) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false) → c ≤ k → c + 1 ≤ S.card → c ≤ ((Finset.range C.size).filter (fun j => (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card := by
  classical
  intro n k c o S C hg hsingle hsparse hck hsize
  change c ≤ count S C.gates
  by_contra h
  have hlt : count S C.gates < c := by omega
  obtain ⟨A,T,ha,ht,hd,hc⟩ := cover S C.gates hg {o}
  simp only [Finset.card_singleton] at ha ht
  have hnot : ¬ S ⊆ A := by
    intro hsa
    have := Finset.card_le_card hsa
    omega
  obtain ⟨p,hp,hpa⟩ := Finset.not_subset.mp hnot
  have hout : wire C.gates (point p) o = true := (hsingle p).2 hp
  have htrue := hc p hp hpa o (Finset.mem_singleton_self _) hout
  have hx : (Finset.univ.filter (fun q => bits T q = true)) = T := by
    ext q
    simp [bits]
  have hfalse := hsparse (bits T) (by rw [hx]; omega) (by
    intro q hq
    have : q ∉ T := fun htq => hd q htq hq
    simp [bits, this])
  change wire C.gates (bits T) o = false at hfalse
  rw [htrue] at hfalse
  contradiction
