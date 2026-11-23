import PEqualNP.Defs
import Mathlib

-- Mythos 6 et Codex Betelgeuse

namespace PEqualNP.Outside.L_meta_925_aux

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_before (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getElem?_append_left hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) :
    (run gs x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun w =>
        if w < x.length + j then (run gs x).getD w false else false) := by
  induction gs generalizing x j with
  | nil => simp at hg
  | cons a gs ih =>
    cases j with
    | zero =>
      have hag : a = g := by simpa using hg
      subst a
      let v := g.op.eval (g.inputs.map fun i => x.getD i false)
      change (run gs (x ++ [v])).getD (x.length + 0) false = _
      rw [run_before gs (x ++ [v]) _ (by simp)]
      have hread : (fun w => if w < x.length + 0 then
          (run (g :: gs) x).getD w false else false) =
          (fun w => x.getD w false) := by
        funext w
        by_cases hw : w < x.length
        · simp only [Nat.add_zero, ite_eq_left hw]
          exact run_before (g :: gs) x w hw
        · simp [hw]
      rw [hread]
      simp [v]
    | succ j =>
      have htail : gs[j]? = some g := by simpa using hg
      let y := x ++ [a.op.eval (a.inputs.map fun i => x.getD i false)]
      have hy : y.length = x.length + 1 := by simp [y]
      have h := ih y j htail
      have hlen : y.length + j = x.length + (j + 1) := by omega
      rw [hlen] at h
      exact h

lemma eval_mono (g : Gate) (f h : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfh : ∀ w ∈ g.inputs, f w = true → h w = true)
    (hf : g.op.eval (g.inputs.map f) = true) :
    g.op.eval (g.inputs.map h) = true := by
  rcases hop with ha | ho
  · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hf ⊢
    intro w hw
    exact hfh w hw (hf w hw)
  · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hf ⊢
    rcases hf with ⟨w, hw, hfw⟩
    exact ⟨w, hw, hfh w hw hfw⟩

lemma append_mono (x y : List Bool) (a b : Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (x ++ [a]).getD i false = true → (y ++ [b]).getD i false = true := by
  intro i hi
  by_cases hix : i < x.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hix] at hi
    have hiy : i < y.length := by omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiy] using hxy i hi
  · have hxle : x.length ≤ i := by omega
    have hyle : y.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hxle] at hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hyle]
    rw [← hlen]
    by_cases he : i = x.length
    · subst i
      simpa using hab (by simpa using hi)
    · have hsub : 1 ≤ i - x.length := by omega
      have hn : ([a] : List Bool)[i - x.length]? = none :=
        List.getElem?_eq_none (by simpa using hsub)
      simp [hn] at hi

lemma run_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    apply ih (by intro a ha; exact hgs a (List.mem_cons_of_mem _ ha))
    · simp [hlen]
    · exact append_mono x y _ _ hlen hxy
        (eval_mono g _ _ (hgs g (by simp)) (by intro w _; exact hxy w))

lemma circuit_mono (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ i, (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  apply run_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  by_cases hin : i < n
  · simp [hin] at hi ⊢
    exact hxy ⟨i, hin⟩ hi
  · simp [hin] at hi

def inputsOf (C : Circuit) (j : ℕ) : List ℕ :=
  match C.gates[j]? with
  | some g => g.inputs
  | none => []

def allInputs (C : Circuit) (Q : Finset ℕ) : Finset ℕ :=
  Q.biUnion (fun j => (inputsOf C j).toFinset)

def boundary (C : Circuit) (n : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  allInputs C Q \ Q.image (fun j => n + j)

lemma boundary_card (C : Circuit) (n r : ℕ) (Q : Finset ℕ)
    (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hr : r ∈ Q)
    (hp : ∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧
      ∃ g : Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) :
    (boundary C n Q).card ≤ Q.card + 1 := by
  have htotal : (allInputs C Q).card ≤ Q.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro j _
    cases hg : C.gates[j]? with
    | none => simp [inputsOf, hg]
    | some g =>
      simpa [inputsOf, hg] using
        (List.toFinset_card_le g.inputs).trans (hC g (List.mem_of_getElem? hg))
  have hsub : (Q.erase r).image (fun j => n + j) ⊆
      allInputs C Q ∩ Q.image (fun j => n + j) := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    rcases Finset.mem_erase.mp hj with ⟨hjr, hjQ⟩
    rcases hp j hjQ hjr with ⟨j', hj'Q, _, g, hg, hin⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_biUnion.mpr
      exact ⟨j', hj'Q, by simp [inputsOf, hg, hin]⟩
    · exact Finset.mem_image.mpr ⟨j, hjQ, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (by
    intro a b hab
    exact Nat.add_left_cancel hab)] at hcard
  have herase := Finset.card_erase_add_one hr
  have hsplit := Finset.card_sdiff_add_card_inter
    (allInputs C Q) (Q.image (fun j => n + j))
  change (allInputs C Q \ Q.image (fun j => n + j)).card ≤ _
  omega

lemma circuit_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun w => if w < n + j then
        (C.wires (List.ofFn x)).getD w false else false) := by
  simpa only [List.length_ofFn, run, Circuit.wires] using run_gate C.gates (List.ofFn x) j g hg

lemma label_sound (C : Circuit) (n : ℕ) (Q : Finset ℕ) (ψ : ℕ → Bool)
    (x : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hsize : ∀ j ∈ Q, j < C.size)
    (hlabel : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map fun w => if w < n + j then ψ w else false))
    (hout : ∀ w ∈ boundary C n Q, (∃ b ∈ Q, w < n+b ∧ ∃ g : Gate, C.gates[b]? = some g ∧ w ∈ g.inputs) → ψ w = true →
      (C.wires (List.ofFn x)).getD w false = true) :
    ∀ j ∈ Q, ψ (n + j) = true →
      (C.wires (List.ofFn x)).getD (n + j) false = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hψj
    have hjlen : j < C.gates.length := hsize j hj
    let g : Gate := C.gates[j]'hjlen
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlen
    rw [circuit_gate C n x j g hg]
    apply eval_mono g (fun w => if w < n + j then ψ w else false)
      (fun w => if w < n + j then (C.wires (List.ofFn x)).getD w false else false)
      (hC g (List.mem_of_getElem? hg))
    · intro w hw hψw
      by_cases hlt : w < n + j
      · simp only [ite_eq_left hlt] at hψw ⊢
        by_cases hwQ : w ∈ Q.image (fun i => n + i)
        · rcases Finset.mem_image.mp hwQ with ⟨i, hiQ, hwi⟩
          have hij : i < j := by omega
          subst w
          exact ih i hij hiQ hψw
        · apply hout w _ ⟨j,hj,hlt,g,hg,hw⟩ hψw
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, hwQ⟩
          exact Finset.mem_biUnion.mpr ⟨j, hj, by simp [inputsOf, hg, hw]⟩
      · simp [hlt] at hψw
    · exact (hlabel j hj g hg).symm.trans hψj


lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons a gs ih =>
    simp only [run, List.foldl_cons]
    change (run gs _).length = _
    rw [ih]
    simp
    omega

open PEqualNP.CircuitLowerBounds

def signal {n : Nat} (C : Circuit) (U : Finset (Fin n)) (w : Nat) :=
  (C.wires (List.ofFn (fun p => decide (p ∈ U)))).getD w false

lemma primary {n : Nat} (C : Circuit) (U : Finset (Fin n)) (w : Nat) (lt : w < n) :
    signal C U w = decide ((⟨w, lt⟩ : Fin n) ∈ U) := by
  change (run C.gates _).getD w false = _
  rw [run_before _ _ _ (by simpa using lt)]
  simp [List.getD_eq_getElem?_getD, lt]

lemma past {n : Nat} (C : Circuit) (U : Finset (Fin n)) (w : Nat) (ge : n+C.size ≤ w) :
    signal C U w = false := by
  change (run C.gates _).getD w false = false
  apply List.getD_eq_default
  rw [run_length, List.length_ofFn]
  exact ge

lemma union_bound {α β : Type} [DecidableEq α] [DecidableEq β] (F : Finset β) (T : β → Finset α)
    (q : Nat) (size : ∀ a ∈ F, (T a).card ≤ q+1)
    (overlap : ∀ a ∈ F, q < (T a).card → ∀ b ∈ F, (T b \ T a).card ≤ q) :
    (F.biUnion T).card ≤ F.card*q+1 := by
  classical
  by_cases large : ∃ a ∈ F, q < (T a).card
  · obtain ⟨a,ha,large⟩ := large
    let R := (F.erase a).biUnion fun b => T b \ T a
    have covered : F.biUnion T ⊆ T a ∪ R := by
      intro x hx
      obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
      by_cases h : x ∈ T a
      · exact Finset.mem_union_left _ h
      · have ne : b ≠ a := fun e => h (e ▸ hx)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨b, Finset.mem_erase.mpr ⟨ne,hb⟩, Finset.mem_sdiff.mpr ⟨hx,h⟩⟩)
    have bound : R.card ≤ (F.erase a).card*q :=
      Finset.card_biUnion_le_card_mul _ _ _ fun b hb => overlap a ha large b (Finset.mem_erase.mp hb).2
    have c1 := Finset.card_le_card covered
    have c2 := Finset.card_union_le (T a) R
    have c3 := size a ha
    have eqn := Finset.card_erase_add_one ha
    rw [← eqn, Nat.add_mul, Nat.one_mul]
    omega
  · have small : ∀ a ∈ F, (T a).card ≤ q := by
      intro a ha
      exact Nat.le_of_not_gt (fun h => large ⟨a,ha,h⟩)
    exact (Finset.card_biUnion_le_card_mul _ _ _ small).trans (by omega)

lemma piece_cost {n m : Nat} (q : Nat) (hq : 2 ≤ q) (S : Fin m → Finset (Fin n)) (i : Fin m)
    (card : ∀ j, (S j).card = q+1)
    (meet : ∀ a b, a ≠ b → (S a ∩ S b).card = 1)
    {β : Type} [Fintype β] [DecidableEq β] (T : β → Finset (Fin n))
    (shape : ∀ t, (T t).card ≤ 1 ∨ ∃ j, j ≠ i ∧ T t = S j) :
    (Finset.univ.biUnion T).card ≤ Fintype.card β*q+1 ∧
    ((Finset.univ.biUnion T) ∩ S i).card ≤ Fintype.card β := by
  classical
  constructor
  · rw [← Finset.card_univ]
    apply union_bound
    · intro a _
      obtain h | ⟨j,_,h⟩ := shape a
      · omega
      · rw [h,card]
    · intro a _ ha b _
      obtain h | ⟨j,_,hj⟩ := shape a
      · omega
      obtain h | ⟨l,_,hl⟩ := shape b
      · exact (Finset.card_le_card (Finset.sdiff_subset : T b \ T a ⊆ T b)).trans (by omega)
      rw [hj,hl]
      by_cases e : l = j
      · simp [e]
      · have eqn := Finset.card_sdiff_add_card_inter (S l) (S j)
        rw [meet l j e,card] at eqn
        omega
  · have sub : (Finset.univ.biUnion T) ∩ S i ⊆ Finset.univ.biUnion (fun t => T t ∩ S i) := by
      intro x hx
      obtain ⟨hU,hS⟩ := Finset.mem_inter.mp hx
      obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hU
      exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,Finset.mem_inter.mpr ⟨hb,hS⟩⟩
    have small : ∀ b ∈ (Finset.univ : Finset β), (T b ∩ S i).card ≤ 1 := by
      intro b _
      obtain h | ⟨j,ne,e⟩ := shape b
      · exact (Finset.card_le_card Finset.inter_subset_left).trans h
      · rw [e, meet j i ne]
    exact (Finset.card_le_card sub).trans (by
      simpa using Finset.card_biUnion_le_card_mul Finset.univ (fun t => T t ∩ S i) 1 small)
open PEqualNP.CircuitLowerBounds

def exclusive {m n : Nat} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) (w : Nat) :=
  signal C (S i) w = true ∧ ∀ j, j ≠ i → signal C (S j) w = false

noncomputable def owner {m n : Nat} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) : Finset Nat := by
  classical
  exact (Finset.range C.size).filter fun j => exclusive C S i (n+j)

lemma owner_mem {m n : Nat} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) (j : Nat) :
    j ∈ owner C S i ↔ j < C.size ∧ exclusive C S i (n+j) := by classical simp [owner]

lemma bound_one {m n : Nat} (q K c : Nat) (hq : 2 ≤ q) (S : Fin m → Finset (Fin n))
    (card : ∀ j, (S j).card = q+1) (meet : ∀ a b, a ≠ b → (S a ∩ S b).card = 1)
    (C : Circuit) (o : Fin m → Nat) (i : Fin m)
    (ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (spec : ∀ j (U : Finset (Fin n)), U.card ≤ K → signal C U (o j) = decide (S j ⊆ U))
    (cq : c ≤ q) (ck : c*q < K) : c ≤ (owner C S i).card := by
  classical
  by_contra! bad
  have leq : q+1 ≤ K := by
    have h : 1*q ≤ c*q := Nat.mul_le_mul_right q (by omega)
    simp only [Nat.one_mul] at h
    omega
  have htrue : signal C (S i) (o i) = true := by
    rw [spec _ _ (by rw [card]; exact leq)]; simp
  have ex : exclusive C S i (o i) := by
    refine ⟨htrue, ?_⟩
    intro j ne
    rw [spec _ _ (by rw [card]; exact leq)]
    apply decide_eq_false
    intro ss
    have e := meet i j ne.symm
    rw [Finset.inter_eq_left.mpr ss, card] at e
    omega
  have lo : n ≤ o i := by
    by_contra! lt
    let v : Fin n := ⟨o i,lt⟩
    have actual : signal C {v} (o i) = true := by rw [primary _ _ _ lt]; simp [v]
    rw [spec _ _ (by simp; omega)] at actual
    have hsub : S i ⊆ {v} := of_decide_eq_true actual
    have size := Finset.card_le_card hsub
    rw [card, Finset.card_singleton] at size
    omega
  have hi : o i < n+C.size := by
    by_contra! ge
    rw [past _ _ _ ge] at htrue
    contradiction
  let r := o i - n
  have eqr : n+r = o i := by dsimp [r]; omega
  let P := owner C S i
  have rP : r ∈ P := (owner_mem _ _ _ _).mpr ⟨by omega, by rwa [eqr]⟩
  let R := fun a b : Nat => a ∈ P ∧ b ∈ P ∧ a < b ∧ ∃ g : Gate, C.gates[b]? = some g ∧ n+a ∈ g.inputs
  let Q := P.filter fun j => Relation.ReflTransGen R j r
  have rQ : r ∈ Q := Finset.mem_filter.mpr ⟨rP,Relation.ReflTransGen.refl⟩
  have sub : Q ⊆ P := Finset.filter_subset _ _
  have sizes (j) (hj : j ∈ Q) : j < C.size := ((owner_mem _ _ _ _).mp (sub hj)).1
  have parent (a) (ha : a ∈ Q) (ne : a ≠ r) :
      ∃ b ∈ Q, a < b ∧ ∃ g : Gate, C.gates[b]? = some g ∧ n+a ∈ g.inputs := by
    have path : Relation.ReflTransGen R a r := (Finset.mem_filter.mp ha).2
    obtain e | ⟨b,ab,br⟩ := path.cases_head
    · exact (ne e).elim
    · exact ⟨b,Finset.mem_filter.mpr ⟨ab.2.1,br⟩,ab.2.2⟩
  let early (w : Nat) : Prop := ∃ b ∈ Q, w < n+b ∧ ∃ g : Gate, C.gates[b]? = some g ∧ w ∈ g.inputs
  let B := (boundary C n Q).filter fun w => early w ∧ signal C (S i) w = true
  have Bcard : B.card ≤ c := by
    have h₁ : B.card ≤ (boundary C n Q).card := Finset.card_le_card (Finset.filter_subset _ _)
    have h₂ := boundary_card C n r Q (fun g hg => (ops g hg).2) rQ parent
    have h₃ : Q.card ≤ (owner C S i).card := Finset.card_le_card sub
    omega
  have witness (w : {w // w ∈ B}) : ∃ T : Finset (Fin n), signal C T w.val = true ∧
      (T.card ≤ 1 ∨ ∃ j, j ≠ i ∧ T = S j) := by
    obtain ⟨bw,hvalid,tw⟩ := Finset.mem_filter.mp w.property
    by_cases input : w.val < n
    · let v : Fin n := ⟨w.val,input⟩
      exact ⟨{v}, by rw [primary _ _ _ input]; simp [v], Or.inl (by simp)⟩
    · by_cases foreign : ∃ j, j ≠ i ∧ signal C (S j) w.val = true
      · obtain ⟨j,ne,hw⟩ := foreign
        exact ⟨S j,hw,Or.inr ⟨j,ne,rfl⟩⟩
      exfalso
      have privateW : exclusive C S i w.val := by
        refine ⟨tw, ?_⟩
        intro j ne
        cases ev : signal C (S j) w.val with
        | false => rfl
        | true => exact False.elim (foreign ⟨j,ne,ev⟩)
      have wl : w.val < n+C.size := by
        by_contra! ge
        rw [past _ _ _ ge] at tw
        contradiction
      let a := w.val - n
      have ea : n+a = w.val := by dsimp [a]; omega
      have aP : a ∈ P := (owner_mem _ _ _ _).mpr ⟨by omega, by rwa [ea]⟩
      obtain ⟨b,hb,earlyW,g,hg,hop⟩ := hvalid
      have ab : R a b := ⟨aP,sub hb,by omega,g,hg,by rwa [ea]⟩
      have aQ : a ∈ Q := Finset.mem_filter.mpr ⟨aP, Relation.ReflTransGen.head ab (Finset.mem_filter.mp hb).2⟩
      exact (Finset.mem_sdiff.mp bw).2 (Finset.mem_image.mpr ⟨a,aQ,ea⟩)
  choose D good using witness
  let U := Finset.univ.biUnion D
  obtain ⟨large,small⟩ := piece_cost q hq S i card meet D (fun w => (good w).2)
  have idx : Fintype.card {w // w ∈ B} = B.card := Fintype.card_coe _
  rw [idx] at large small
  have uK : U.card ≤ K := by
    change U.card ≤ B.card * q + 1 at large
    have := Nat.mul_le_mul_right q Bcard
    omega
  have missing : ¬ S i ⊆ U := by
    intro ss
    have e : U ∩ S i = S i := Finset.inter_eq_right.mpr ss
    change (U ∩ S i).card ≤ B.card at small
    rw [e,card] at small
    omega
  have forced := label_sound C n Q (signal C (S i)) (fun p => decide (p ∈ U))
    (fun g hg => (ops g hg).1) sizes
    (fun j _ g hg => circuit_gate C n (fun p => decide (p ∈ S i)) j g hg)
    (by
      intro w hw e ht
      let t : {v // v ∈ B} := ⟨w, Finset.mem_filter.mpr ⟨hw,e,ht⟩⟩
      apply circuit_mono C (fun g hg => (ops g hg).1) n (fun p => decide (p ∈ D t)) _ _ w (good t).1
      intro z hz
      exact decide_eq_true (Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,of_decide_eq_true hz⟩)) r rQ (by rwa [eqr])
  change signal C U (n+r) = true at forced
  rw [eqr,spec i U uK] at forced
  exact missing (of_decide_eq_true forced)

end PEqualNP.Outside.L_meta_925_aux

open PEqualNP.Outside.L_meta_925_aux in
theorem PEqualNP.Outside.L_meta_925 :
∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq sizes meet gates out ops correct c cq ck
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,0⟩
  have spec (i : Fin m) (U : Finset (Fin n)) (hU : U.card ≤ K) :
      signal C U (out i) = decide (S i ⊆ U) := by
    have h := correct i (fun p => decide (p ∈ U)) (by simpa using hU)
    change signal C U (out i) = _ at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rfl
  let P := fun i => owner C S i
  have distinct : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro a hi hj
    obtain ⟨_,t,abs⟩ := (owner_mem C S i a).mp hi
    have pos := ((owner_mem C S j a).mp hj).2.1
    rw [abs j ne.symm] at pos
    contradiction
  calc
    m*c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (P i).card := Finset.sum_le_sum fun i _ => bound_one q K c hq S sizes meet C out i ops spec cq ck
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion distinct).symm
    _ ≤ (Finset.range C.size).card := Finset.card_le_card (by
      intro a ha
      obtain ⟨i,_,g⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_range.mpr ((owner_mem C S i a).mp g).1)
    _ = gates.length := Finset.card_range _
