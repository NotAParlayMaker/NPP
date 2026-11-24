import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3473

-- Compile a zeroed wire to none, and every surviving wire to its new index.
private def port (p : List (Option ℕ)) (i : ℕ) := p.getD i none
private def start (n v : ℕ) : List (Option ℕ) := List.ofFn fun i : Fin n =>
  if i.val = v then none else some i.val

private def pins (g : Gate) : ℕ × ℕ := (g.inputs.getD 0 0,g.inputs.getD 1 0)

private def andTag (g : Gate) : Bool := match g.op with
  | .and => true
  | _ => false

private def foldGate (p : List (Option ℕ)) (g : Gate) : Option ℕ ⊕ Gate :=
  let a := port p (pins g).1
  let b := port p (pins g).2
  match a,b with
  | some i,some j => .inr ⟨g.op,[i,j]⟩
  | _,_ => .inl (if andTag g then none else a.or b)

private def pack : List Gate → List (Option ℕ) → ℕ → List Gate × List (Option ℕ)
  | [],p,_ => ([],p)
  | g :: gs,p,n =>
    match foldGate p g with
    | .inl a => pack gs (p ++ [a]) n
    | .inr h =>
      let rest := pack gs (p ++ [some n]) (n+1)
      (h :: rest.1,rest.2)

private def Simple (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private def Fit (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), Simple gs[j] ∧ ∀ i ∈ gs[j].inputs, i < n+j

private def Bounded (p : List (Option ℕ)) (n : ℕ) : Prop :=
  ∀ i j, port p i = some j → j<n

private theorem arity (g : Gate) (hg : Simple g) :
    ∃ a b, g.inputs = [a,b] ∧ pins g = (a,b) := by
  have h := hg.2
  cases e : g.inputs with
  | nil => simp [e] at h
  | cons a as =>
    cases as with
    | nil => simp [e] at h
    | cons b bs =>
      have h0 : bs = [] := by simpa [e] using h
      subst bs
      exact ⟨a,b,rfl,by simp [pins,e]⟩

private theorem fit_cons (n : ℕ) (g : Gate) (gs : List Gate)
    (hg : Simple g ∧ ∀ i ∈ g.inputs, i<n) (hs : Fit (n+1) gs) :
    Fit n (g::gs) := by
  intro j hj
  cases j with
  | zero => simpa using hg
  | succ j =>
    have ht : j < gs.length := by simpa using hj
    simpa [Nat.add_assoc,Nat.add_comm 1 j] using hs j ht

private theorem fit_ao (n : ℕ) (C : Circuit) (hC : Fit n C.gates) : IsAO2 n C := by
  have all (g : Gate) (hg : g ∈ C.gates) : Simple g := by
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
    rw [← he]
    exact (hC j hj).1
  refine ⟨fun g hg => (all g hg).1, ?_, fun g hg => (all g hg).2⟩
  intro j hj i hi
  have e : NestedCover.gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [e] at hi
  exact (hC j hj).2 i hi

private theorem read_old {α : Type} (p : List α) (x d : α) (i : ℕ) (h : i ≠ p.length) :
    (p ++ [x]).getD i d = p.getD i d := by
  by_cases hi : i < p.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private theorem read_last {α : Type} (p : List α) (x d : α) :
    (p ++ [x]).getD p.length d = x := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

private theorem get_start (n v i : ℕ) :
    port (start n v) i = if i < n ∧ i ≠ v then some i else none := by
  simp only [port,start,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  split_ifs <;> simp_all

private theorem port_old (p : List (Option ℕ)) (a : Option ℕ) (i : ℕ) (h : i ≠ p.length) :
    port (p ++ [a]) i = port p i := read_old _ _ _ _ h

private theorem port_last (p : List (Option ℕ)) (a : Option ℕ) :
    port (p ++ [a]) p.length = a := read_last _ _ _

private theorem bounded_push (p : List (Option ℕ)) (n : ℕ) (a : Option ℕ)
    (hp : Bounded p n) (ha : ∀ j, a = some j → j<n) : Bounded (p ++ [a]) n := by
  intro i j h
  by_cases hi : i=p.length
  · rw [hi,port_last] at h
    exact ha _ h
  · rw [port_old _ _ _ hi] at h
    exact hp _ _ h

private theorem folded_alias (p : List (Option ℕ)) (n : ℕ) (g : Gate) (a : Option ℕ)
    (h : foldGate p g = .inl a) (hp : Bounded p n) :
    ∀ j, a = some j → j < n := by
  intro j hj
  subst a
  cases h0 : port p (pins g).1 <;> cases h1 : port p (pins g).2 <;>
    simp [foldGate,h0,h1] at h
  all_goals
    obtain ⟨_,rfl⟩ := h
    first | exact hp _ _ h0 | exact hp _ _ h1

private theorem folded_fit (p : List (Option ℕ)) (n : ℕ) (g q : Gate)
    (hg : Simple g) (h : foldGate p g = .inr q) (hp : Bounded p n) :
    Simple q ∧ ∀ i ∈ q.inputs, i<n := by
  cases h0 : port p (pins g).1 <;> cases h1 : port p (pins g).2 <;>
    simp [foldGate,h0,h1] at h
  subst q
  refine ⟨⟨hg.1,rfl⟩,?_⟩
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl
  · exact hp _ _ h0
  · exact hp _ _ h1

private theorem pack_fit (gs : List Gate) (p : List (Option ℕ)) (n : ℕ)
    (hg : ∀ g ∈ gs, Simple g) (hp : Bounded p n) : Fit n (pack gs p n).1 := by
  induction gs generalizing p n with
  | nil => simp [pack,Fit]
  | cons g gs ih =>
    simp only [pack]
    have tail : ∀ q ∈ gs, Simple q := fun q hq => hg q (by simp [hq])
    split
    · rename_i a ha
      exact ih _ _ tail (bounded_push _ _ _ hp (folded_alias _ _ _ _ ha hp))
    · rename_i h hh
      apply fit_cons _ _ _ (folded_fit _ _ _ _ (hg g (by simp)) hh hp)
      exact ih _ _ tail (bounded_push _ _ _
        (fun i j h => (hp i j h).trans (Nat.lt_succ_self _)) (fun j h => Nat.lt_succ_of_le (Option.some.inj h).symm.le))

private theorem pack_size (gs : List Gate) (p : List (Option ℕ)) (n : ℕ) :
    (pack gs p n).1.length ≤ gs.length := by
  induction gs generalizing p n with
  | nil => simp [pack]
  | cons g gs ih =>
    simp only [pack]
    split
    · exact (ih _ _).trans (by simp)
    · simpa using Nat.succ_le_succ (ih _ _)

private theorem pack_drop (gs : List Gate) (p : List (Option ℕ)) (n v : ℕ)
    (hv : v < p.length) (noneAt : port p v = none) (hg : ∀ g ∈ gs, Simple g)
    (reads : ∃ g ∈ gs, v ∈ g.inputs) : (pack gs p n).1.length < gs.length := by
  induction gs generalizing p n with
  | nil => simp at reads
  | cons g gs ih =>
    have gsimple := hg g (by simp)
    have tail : ∀ q ∈ gs, Simple q := fun q hq => hg q (by simp [hq])
    have lt (a : Option ℕ) : v < (p ++ [a]).length := by simp; omega
    have keep (a : Option ℕ) : port (p ++ [a]) v = none :=
      (port_old _ _ _ (by omega)).trans noneAt
    by_cases h : v ∈ g.inputs
    · obtain ⟨a,b,hp,hpin⟩ := arity g gsimple
      rw [hp] at h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      have remove : ∃ a, foldGate p g = .inl a := by
        rcases h with he | he
        · cases hb : port p (pins g).2 <;> simp [foldGate,hpin,← he,noneAt] at *
        · cases ha : port p (pins g).1 <;> simp [foldGate,hpin,← he,noneAt] at *
      obtain ⟨a,ha⟩ := remove
      rw [pack,ha]
      exact Nat.lt_succ_of_le (pack_size _ _ _)
    · obtain ⟨q,hq,hr⟩ := reads
      have real : ∃ q ∈ gs, v ∈ q.inputs :=
        ⟨q,(List.mem_cons.mp hq).resolve_left (fun e => h (e ▸ hr)),hr⟩
      simp only [pack]
      split
      · exact (ih _ _ (lt _) (keep _) tail real).trans_le (by simp)
      · simpa using Nat.succ_lt_succ (ih _ _ (lt _) (keep _) tail real)

private def get {α : Type} (z : α) (w : List α) : Option ℕ → α
  | none => z
  | some i => w.getD i z

private def evalGate {α : Type} (z : α) (A O : α → α → α) (w : List α) (g : Gate) :=
  (if andTag g then A else O) (w.getD (pins g).1 z) (w.getD (pins g).2 z)

private def step {α : Type} (z : α) (A O : α → α → α) (w : List α) (g : Gate) :=
  w ++ [evalGate z A O w g]

private def run {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) :=
  gs.foldl (step z A O) x

private def ZeroLaws {α : Type} (z : α) (A O : α → α → α) : Prop :=
  (∀ a, A z a = z) ∧ (∀ a, A a z = z) ∧ (∀ a, O z a = a) ∧ (∀ a, O a z = a)

private theorem run_len {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) :
    (run z A O gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run z A O gs (step z A O x g)).length = _
    rw [ih]
    simp [step]
    omega

private def Agree {α : Type} (z : α) (p : List (Option ℕ)) (w v : List α) : Prop :=
  p.length = w.length ∧ ∀ i, w.getD i z = get z v (port p i)

private theorem eval_fold {α : Type} (z : α) (A O : α → α → α) (hl : ZeroLaws z A O)
    (p : List (Option ℕ)) (w v : List α) (g : Gate) (h : Agree z p w v) :
    evalGate z A O w g =
      (foldGate p g).elim (get z v) (evalGate z A O v) := by
  obtain ⟨az,za,oz,zo⟩ := hl
  have keep (a b : ℕ) :
      evalGate z A O v ⟨g.op,[a,b]⟩ =
        (if andTag g then A else O) (v.getD a z) (v.getD b z) := rfl
  change (if andTag g then A else O) (w.getD (pins g).1 z) (w.getD (pins g).2 z) = _
  rw [h.2,h.2]
  cases ha : port p (pins g).1 <;> cases hb : port p (pins g).2 <;>
    cases hg : andTag g <;>
    simp [foldGate,ha,hb,hg,get,keep,az,za,oz,zo]

private theorem get_stable {α : Type} (z : α) (v : List α) (b : α)
    (p : List (Option ℕ)) (hp : Bounded p v.length) (i : ℕ) :
    get z (v ++ [b]) (port p i) = get z v (port p i) := by
  cases h : port p i with
  | none => rfl
  | some j => exact List.getD_append _ _ _ _ (hp _ _ h)

private theorem pack_agree {α : Type} (z : α) (A O : α → α → α) (hl : ZeroLaws z A O)
    (gs : List Gate) (p : List (Option ℕ)) (w v : List α)
    (h : Agree z p w v) (hp : Bounded p v.length) :
    Agree z (pack gs p v.length).2 (run z A O gs w)
      (run z A O (pack gs p v.length).1 v) := by
  induction gs generalizing p w v with
  | nil => exact h
  | cons g gs ih =>
    simp only [pack]
    have eg := eval_fold z A O hl p w v g h
    split
    · rename_i a ha
      rw [ha] at eg
      change Agree z (pack gs (p ++ [a]) v.length).2 (run z A O gs (step z A O w g))
        (run z A O (pack gs (p ++ [a]) v.length).1 v)
      apply ih
      · refine ⟨by simp [step,h.1],?_⟩
        intro i
        by_cases hi : i=p.length
        · rw [hi,port_last,h.1]
          exact (read_last _ _ _).trans eg
        · rw [port_old _ _ _ hi]
          change (w ++ [_]).getD i z = _
          rw [read_old _ _ _ _ (by simpa [h.1] using hi)]
          exact h.2 i
      · exact bounded_push _ _ _ hp (folded_alias _ _ _ _ ha hp)
    · rename_i q hq
      rw [hq] at eg
      change Agree z (pack gs (p ++ [some v.length]) (v.length+1)).2
        (run z A O gs (step z A O w g))
        (run z A O (pack gs (p ++ [some v.length]) (v.length+1)).1 (step z A O v q))
      have len : (step z A O v q).length = v.length+1 := by simp [step]
      simp only [← len]
      apply ih
      · refine ⟨by simp [step,h.1],?_⟩
        intro i
        by_cases hi : i=p.length
        · rw [hi,port_last,h.1]
          change (w ++ [_]).getD w.length z = (v ++ [_]).getD v.length z
          rw [read_last,read_last]
          exact eg
        · rw [port_old _ _ _ hi]
          have e := get_stable z v (evalGate z A O v q) p hp i
          change (w ++ [_]).getD i z = get z (v ++ [_]) (port p i)
          rw [e,read_old _ _ _ _ (by simpa [h.1] using hi)]
          exact h.2 i
      · rw [len]
        exact bounded_push _ _ _
          (fun i j e => (hp i j e).trans (Nat.lt_succ_self _))
          (fun j e => by have h' := Option.some.inj e; omega)

private theorem run_rel {α : Type} (z : α) (A O : α → α → α)
    (R : α → α → Prop) (P : ℕ → Prop) (_refl : R z z)
    (andOK : ∀ a b c d, R a c → R b d → R (A a b) (A c d))
    (orOK : ∀ a b c d, R a c → R b d → R (O a b) (O c d))
    (gs : List Gate) (w v : List α) (len : w.length=v.length)
    (uses : ∀ g ∈ gs, P (pins g).1 ∧ P (pins g).2)
    (h : ∀ i, P i → R (w.getD i z) (v.getD i z)) :
    ∀ i, P i → R ((run z A O gs w).getD i z) ((run z A O gs v).getD i z) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i, P i → R ((run z A O gs (step z A O w g)).getD i z)
      ((run z A O gs (step z A O v g)).getD i z)
    apply ih _ _ (by simp [step,len]) (fun q hq => uses q (by simp [hq]))
    intro i hi
    have hg := uses g (by simp)
    by_cases e : i = w.length
    · have e' : i=v.length := e.trans len
      change R ((w ++ [_]).getD i z) ((v ++ [_]).getD i z)
      rw [show (w ++ [evalGate z A O w g]).getD i z = evalGate z A O w g from
        e ▸ read_last _ _ _,show (v ++ [evalGate z A O v g]).getD i z =
          evalGate z A O v g from e' ▸ read_last _ _ _]
      unfold evalGate
      split
      · exact andOK _ _ _ _ (h _ hg.1) (h _ hg.2)
      · exact orOK _ _ _ _ (h _ hg.1) (h _ hg.2)
    · change R ((w ++ [_]).getD i z) ((v ++ [_]).getD i z)
      rw [read_old _ _ _ _ e,read_old _ _ _ _ (fun h => e (h.trans len.symm))]
      exact h i hi

private theorem eval_congr {α : Type} (gs : List Gate)
    (f h : List α → Gate → List α) (agree : ∀ g ∈ gs, ∀ w, f w g = h w g)
    (w : List α) : gs.foldl f w = gs.foldl h w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,agree g (by simp)]
    exact ih (fun q hq => agree q (by simp [hq])) _

private theorem bool_eval (C : Circuit) (hg : ∀ g ∈ C.gates, Simple g) (w : List Bool) :
    C.wires w = run false (· && ·) (· || ·) C.gates w := by
  unfold Circuit.wires run
  apply eval_congr
  intro g h v
  obtain ⟨a,b,hi,hpins⟩ := arity g (hg g h)
  rcases (hg g h).1 with hop | hop <;>
    simp [step,evalGate,andTag,hop,hi,hpins,GateOp.eval]

private def andPair (a b : Bool × Bool) : Bool × Bool :=
  (a.1 && b.1,(a.1 && b.2) || (a.2 && b.1))

private def orPair (a b : Bool × Bool) : Bool × Bool :=
  (a.1 || b.1,a.2 || b.2)

private def pairIn (L : ℕ → Bool) (w : List Bool) : List (Bool × Bool) :=
  w.zipIdx.map (fun (b,i) => if L i then (false,b) else (b,false))

private theorem pair_eval (C : Circuit) (hg : ∀ g ∈ C.gates, Simple g)
    (L : ℕ → Bool) (w : List Bool) :
    PEqualNP.ReadK.linearParts C L w = run (false,false) andPair orPair C.gates (pairIn L w) := by
  unfold PEqualNP.ReadK.linearParts run pairIn
  apply eval_congr
  intro g h v
  obtain ⟨a,b,hi,hpins⟩ := arity g (hg g h)
  rcases (hg g h).1 with hop | hop <;>
    simp [step,evalGate,andTag,hop,hi,hpins,andPair,orPair]

private theorem bool_laws : ZeroLaws false (· && ·) (· || ·) := by
  simp [ZeroLaws]

private theorem pair_laws : ZeroLaws (false,false) andPair orPair := by
  simp [ZeroLaws,andPair,orPair]

private theorem ofFn_read {α : Type} (x : Fin n → α) (z : α) (i : ℕ) :
    (List.ofFn x).getD i z = if h : i<n then x ⟨i,h⟩ else z := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  split <;> rfl

private theorem init_agree {α : Type} (z : α) (n v : ℕ) (w u : List α)
    (h1 : w.length=n) (h2 : u.length=n) (hz : w.getD v z = z)
    (hEq : ∀ i, i<n → i≠v → w.getD i z = u.getD i z) :
    Agree z (start n v) w u := by
  refine ⟨by simp [start,h1],?_⟩
  intro i
  rw [get_start]
  split
  · rename_i hi
    exact hEq _ hi.1 hi.2
  · rename_i hi
    by_cases h : i=v
    · subst i; exact hz
    · exact List.getD_eq_default _ _ (by rw [h1]; omega)

private theorem init_bound (n v : ℕ) : Bounded (start n v) n := by
  intro i j e
  rw [get_start] at e
  split at e
  · rename_i h
    cases e
    exact h.1
  · cases e

private def reduced (n v : ℕ) (C : Circuit) : Circuit :=
  let R := pack C.gates (start n v) n
  ⟨R.1,(port R.2 C.output).getD (n+R.1.length)⟩

private theorem output_eval {α : Type} (z : α) (A O : α → α → α) (hl : ZeroLaws z A O)
    (n v : ℕ) (C : Circuit) (w u : List α) (hu : u.length=n)
    (agree : Agree z (start n v) w u) :
    (run z A O C.gates w).getD C.output z =
      (run z A O (reduced n v C).gates u).getD (reduced n v C).output z := by
  let R := pack C.gates (start n v) n
  have hr := pack_agree z A O hl C.gates (start n v) w u agree
    (by rw [hu]; exact init_bound _ _)
  rw [hu] at hr
  change (run z A O C.gates w).getD C.output z =
    (run z A O R.1 u).getD ((port R.2 C.output).getD (n+R.1.length)) z
  have h := hr.2 C.output
  change _ = get z (run z A O R.1 u) (port R.2 C.output) at h
  cases e : port R.2 C.output with
  | none =>
    rw [e] at h
    have zero : (run z A O R.1 u).getD (n+R.1.length) z = z :=
      List.getD_eq_default _ _ (by rw [run_len,hu])
    change (run z A O C.gates w).getD C.output z = (run z A O R.1 u).getD (n+R.1.length) z
    rw [zero]
    exact h
  | some i =>
    rw [e] at h
    exact h

end PEqualNP.Outside.L_meta_3473

open PEqualNP.Outside.L_meta_3473 in
theorem PEqualNP.Outside.L_meta_3473 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x3 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x6 : Fin x1) => Decidable.decide (x6 = x3)) = Bool.false → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size < x2.size ∧ (∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true) ∧ (∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 x8) ∧ ∀ (x8 : ℕ → Bool) (x9 x10 : ℕ), ↑x3 ≠ x9 → ↑x3 ≠ x10 → PEqualNP.ReadK.lineSingle x7 x1 x8 x9 x10 = PEqualNP.ReadK.lineSingle x2 x1 x8 x9 x10 := by
  intro n C v hC essential hsingle
  have hsimple (g : Gate) (hg : g ∈ C.gates) : Simple g := ⟨hC.1 g hg,hC.2.2 g hg⟩
  have out_away : C.output ≠ v.val := by
    intro ho
    have hh : (C.wires (List.ofFn fun i : Fin n => decide (i=v))).getD v.val false = true := by
      have preserve (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i<x.length) :
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).getD
            i false = x.getD i false := by
        induction gs generalizing x with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons,ih _ (by simp; omega)]
          exact List.getD_append _ _ _ _ hi
      rw [Circuit.wires,preserve _ _ _ (by simp [v.isLt]),ofFn_read,dite_eq_left v.isLt]
      simp
    change (C.wires _).getD C.output false = false at hsingle
    rw [ho,hh] at hsingle
    contradiction
  have reader : ∃ g ∈ C.gates, v.val ∈ g.inputs := by
    by_contra! hno
    obtain ⟨x,y,hxy,hneq⟩ := essential
    apply hneq
    change (C.wires (List.ofFn x)).getD C.output false =
      (C.wires (List.ofFn y)).getD C.output false
    rw [bool_eval C hsimple,bool_eval C hsimple]
    apply run_rel false (· && ·) (· || ·) Eq (fun i => i ≠ v.val) rfl
      (by intro a b c d e f; rw [e,f]) (by intro a b c d e f; rw [e,f]) _ _ _
      (by simp) ?_ ?_ _ out_away
    · intro g hg
      obtain ⟨a,b,hi,he⟩ := arity g (hsimple g hg)
      rw [he]
      refine ⟨fun e => hno g hg (by rw [hi]; simp only [List.mem_cons,List.not_mem_nil,or_false]; exact Or.inl e.symm),
        fun e => hno g hg (by rw [hi]; simp only [List.mem_cons,List.not_mem_nil,or_false]; exact Or.inr e.symm)⟩
    · intro i hi
      rw [ofFn_read,ofFn_read]
      split
      · exact hxy _ (fun e => hi (congrArg Fin.val e))
      · rfl
  let D := reduced n v.val C
  have fit := pack_fit C.gates (start n v.val) n hsimple (init_bound n v.val)
  have hD : IsAO2 n D := fit_ao n D fit
  have dsimple (g : Gate) (hg : g ∈ D.gates) : Simple g := ⟨hD.1 g hg,hD.2.2 g hg⟩
  have small : D.size < C.size := pack_drop _ _ _ _ (by simp [start,v.isLt])
    (by simp [get_start]) hsimple reader
  let clear (x : Fin n → Bool) (i : Fin n) := if i=v then false else x i
  have cofactor (x : Fin n → Bool) : circuitFun n D x = circuitFun n C (clear x) := by
    change (D.wires (List.ofFn x)).getD D.output false =
      (C.wires (List.ofFn (clear x))).getD C.output false
    rw [bool_eval D dsimple,bool_eval C hsimple]
    symm
    refine output_eval false (· && ·) (· || ·) bool_laws n v.val C _ _ (by simp) ?_
    apply init_agree _ _ _ _ _ (by simp) (by simp)
    · rw [ofFn_read,dite_eq_left v.isLt]; simp [clear]
    · intro i hi hne
      rw [ofFn_read,ofFn_read,dite_eq_left hi,dite_eq_left hi]
      exact ite_eq_right (fun e => hne (congrArg Fin.val e))
  refine ⟨D,hD,small,?_,?_,?_⟩
  · intro x hx
    rw [cofactor] at hx
    change (C.wires (List.ofFn (clear x))).getD C.output false = true at hx
    change (C.wires (List.ofFn x)).getD C.output false = true
    rw [bool_eval C hsimple] at hx ⊢
    refine run_rel false (· && ·) (· || ·) (fun a b => a=true → b=true)
      (fun _ => True) (by simp) ?_ ?_ _ _ _ (by simp) (by simp) ?_ _ trivial hx
    · simp only [Bool.and_eq_true]
      intro a b c d ac bd h
      exact ⟨ac h.1,bd h.2⟩
    · simp only [Bool.or_eq_true]
      intro a b c d ac bd h
      exact h.elim (fun t => Or.inl (ac t)) (fun t => Or.inr (bd t))
    · intro i _
      rw [ofFn_read,ofFn_read]
      split <;> simp [clear]
  · intro x hx
    rw [cofactor]
    suffices clear x = x by rw [this]
    funext i
    by_cases hi : i=v
    · subst i; simp [clear,hx]
    · simp [clear,hi]
  · intro L p l hp hl
    unfold PEqualNP.ReadK.lineSingle
    rw [pair_eval D dsimple,pair_eval C hsimple]
    congr 1
    let x := pairIn L ((List.range n).map fun i => i == p || i == l)
    symm
    refine output_eval (false,false) andPair orPair pair_laws n v.val C x x (by simp [x,pairIn]) ?_
    apply init_agree _ _ _ _ _ (by simp [x,pairIn]) (by simp [x,pairIn])
    · have ep := beq_eq_false_iff_ne.mpr hp
      have el := beq_eq_false_iff_ne.mpr hl
      simp [x,pairIn,List.getD_eq_getElem?_getD,v.isLt,ep,el]
    · intro i _ _; rfl
