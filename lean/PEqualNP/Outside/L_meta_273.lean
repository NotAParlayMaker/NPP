import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_273_aux
open PEqualNP.CircuitLowerBounds

private abbrev Mask := BitVec 6

private def goalMask : Fin 3 → Mask := ![7,28,49]
private def goals : Finset Mask := {7,28,49}
private def init : List Mask := [1,2,4,8,16,32]
private def allowed (w : List Mask) : Finset Mask := insert 0 w.toFinset


private def fixed : Finset Mask := allowed init ∪ goals
private def pairs : Fin 3 → Finset Mask := ![{3,5,6},{12,20,24},{17,33,48}]

private lemma fixed_card : fixed.card=10 := by decide
private lemma input_card : (allowed init).card=7 := by decide
private lemma separate : ∀ i, goalMask i ∉ allowed init := by decide
private lemma target_mem : ∀ i, goalMask i ∈ goals := by decide
private lemma pair_outside : ∀ i x, x ∈ pairs i → x ∉ fixed := by decide

set_option maxHeartbeats 2000000 in
private lemma union_aux : ∀ (i : Fin 3) (x y : Mask), x≠goalMask i → y≠goalMask i →
    x ||| y = goalMask i → x∈pairs i ∨ y∈pairs i := by decide +kernel

set_option maxHeartbeats 2000000 in
private lemma inter_aux : ∀ (i : Fin 3) (x y : Mask), x≠goalMask i → y≠goalMask i →
    x &&& y = goalMask i → x ≠ y ∧ x ∉ fixed ∧ y ∉ fixed := by decide +kernel

set_option maxHeartbeats 2000000 in
private lemma two_insufficient : ∀ a b : Mask,
    ¬ (∀ i : Fin 3, a ∈ pairs i ∨ b ∈ pairs i ∨ a &&& b = goalMask i) := by decide +kernel

private def joinMask (op : GateOp) (a b : Mask) := match op with
  | .and => a &&& b
  | _ => a ||| b

private def value (w : List Mask) (g : Gate) :=
  joinMask g.op (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0)

private def step (w : List Mask) (g : Gate) := w ++ [value w g]

private lemma read_allowed (w : List Mask) (j : ℕ) : w.getD j 0 ∈ allowed w := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[j]? with
  | none => simp [allowed]
  | some a => simp [allowed,List.mem_of_getElem? h]

private lemma allowed_step (w : List Mask) (g : Gate) :
    allowed (step w g)=insert (value w g) (allowed w) := by
  ext x
  simp [allowed,step]
  tauto


private def formed (s : Finset Mask) (t : Mask) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x≠t ∧ y≠t ∧ (x ||| y=t ∨ x &&& y=t)

private lemma formed_mono {s t : Finset Mask} (h : s ⊆ t) {v : Mask} : formed s v → formed t v := by
  rintro ⟨x,hx,y,hy,rest⟩
  exact ⟨x,h hx,y,h hy,rest⟩

private lemma invariant (gs : List Gate) (w : List Mask)
    (hs : ∀ x∈allowed w, x ∈ allowed init ∨ formed (allowed w) x) :
    ∀ x∈allowed (gs.foldl step w), x ∈ allowed init ∨ formed (allowed (gs.foldl step w)) x := by
  induction gs generalizing w with
  | nil => exact hs
  | cons g rest ih =>
    apply ih
    intro v hv
    rw [allowed_step] at hv ⊢
    have old : allowed w ⊆ insert (value w g) (allowed w) := Finset.subset_insert _ _
    by_cases prev : v∈allowed w
    · exact (hs v prev).imp_right (formed_mono old)
    · obtain rfl := (Finset.mem_insert.mp hv).resolve_right prev
      let x := w.getD (g.inputs.getD 0 0) 0
      let y := w.getD (g.inputs.getD 1 0) 0
      have hx : x∈allowed w := read_allowed w _
      have hy : y∈allowed w := read_allowed w _
      refine Or.inr ⟨x,old hx,y,old hy,fun e => prev (e ▸ hx),fun e => prev (e ▸ hy),?_⟩
      cases h : g.op <;> simp [value,x,y,joinMask,h]

private lemma bounds (gs : List Gate) (w : List Mask) :
    allowed w ⊆ allowed (gs.foldl step w) ∧
    (allowed (gs.foldl step w)).card ≤ (allowed w).card+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g tail ih =>
    obtain ⟨sub,count⟩ := ih (step w g)
    rw [allowed_step] at count sub
    refine ⟨(Finset.subset_insert _ _).trans sub,?_⟩
    have h := Finset.card_insert_le (value w g) (allowed w)
    simp only [List.foldl_cons,List.length_cons]
    omega

private lemma couple (s : Finset Mask) (h : s.card ≤ 2) : ∃ a b : Mask, s ⊆ {a,b} := by
  by_cases ht : s.card=2
  · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp ht
    exact ⟨a,b,Finset.Subset.rfl⟩
  by_cases hn : s.Nonempty
  · obtain ⟨a,ha⟩ := hn
    refine ⟨a,a,fun x hx => ?_⟩
    have eq := (Finset.card_le_one_iff.mp (show s.card ≤ 1 by omega)) hx ha
    simp [eq]
  · exact ⟨0,0,fun x hx => (hn ⟨x,hx⟩).elim⟩

private lemma impossible (w : List Mask) (hinput : allowed init ⊆ allowed w)
    (hg : goals ⊆ allowed w) (cap : (allowed w).card ≤ 12)
    (formed' : ∀ t ∈ allowed w, t ∈ allowed init ∨ formed (allowed w) t) : False := by
  let S := allowed w
  have hfixed : fixed ⊆ S := Finset.union_subset hinput hg
  have card := Finset.card_sdiff_add_card_eq_card hfixed
  rw [fixed_card] at card
  have htwo : (S \ fixed).card ≤ 2 := by change S.card ≤ 12 at cap; omega
  obtain ⟨a,b,sub⟩ := couple _ htwo
  apply two_insufficient a b
  intro i
  obtain ⟨x,hx,y,hy,nx,ny,ho|ha⟩ := (formed' _ (hg (target_mem i))).resolve_left (separate i)
  · rcases union_aux i x y nx ny ho with px|py
    · have mem := sub (Finset.mem_sdiff.mpr ⟨hx,pair_outside i x px⟩)
      rcases Finset.mem_insert.mp mem with rfl|hy'
      · exact Or.inl px
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp hy' ▸ px))
    · have mem := sub (Finset.mem_sdiff.mpr ⟨hy,pair_outside i y py⟩)
      rcases Finset.mem_insert.mp mem with rfl|hx'
      · exact Or.inl py
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp hx' ▸ py))
  · obtain ⟨ne,ox,oy⟩ := inter_aux i x y nx ny ha
    have mx := sub (Finset.mem_sdiff.mpr ⟨hx,ox⟩)
    have my := sub (Finset.mem_sdiff.mpr ⟨hy,oy⟩)
    simp only [Finset.mem_insert,Finset.mem_singleton] at mx my
    rcases mx with rfl|rfl <;> rcases my with rfl|rfl
    · exact (ne rfl).elim
    · exact Or.inr (Or.inr ha)
    · exact Or.inr (Or.inr (by rw [BitVec.and_comm]; exact ha))
    · exact (ne rfl).elim
private def good (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length=2

private def bit (p : Fin 6) (x : Mask) := x.getLsbD p.val

private lemma bit_read (p : Fin 6) (w : List Mask) (j : ℕ) :
    (w.map (bit p)).getD j false=bit p (w.getD j 0) := by
  simpa [bit] using List.getD_map (n := j) w 0 (bit p)

private lemma two_inputs (g : Gate) (h : good g) : ∃ a b, g.inputs=[a,b] := by
  have len := h.2
  cases eq : g.inputs with
  | nil => simp [eq] at len
  | cons a t =>
    cases t with
    | nil => simp [eq] at len
    | cons b u =>
      have z : u=[] := by simpa [eq] using len
      exact ⟨a,b,by simp [z]⟩

private lemma step_bits (p : Fin 6) (w : List Mask) (g : Gate) (h : good g) :
    (step w g).map (bit p) = w.map (bit p) ++
      [g.op.eval (g.inputs.map (fun j => (w.map (bit p)).getD j false))] := by
  obtain ⟨a,b,eq⟩ := two_inputs g h
  rcases h.1 with op|op <;>
    simp [step,value,eq,op,joinMask,GateOp.eval,bit] <;>
    cases ea : w[a]? <;> cases eb : w[b]? <;> simp [bit]

private lemma fold_bits (p : Fin 6) (gs : List Gate) (w : List Mask) (h : ∀ g∈gs,good g) :
    (gs.foldl step w).map (bit p) =
      gs.foldl (fun bs (g : Gate) => bs ++ [g.op.eval (g.inputs.map (fun j => bs.getD j false))]) (w.map (bit p)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    rw [ih (step w g) (fun q hq => h q (List.mem_cons_of_mem _ hq)),step_bits p w g (h g (List.mem_cons_self ..))]

private lemma init_bits : ∀ p : Fin 6, init.map (bit p)=List.ofFn (fun q : Fin 6 => decide (q=p)) := by decide

private def triple : Fin 3 → Finset (Fin 6) := ![{0,1,2},{2,3,4},{4,5,0}]

private lemma goal_bits : ∀ (i : Fin 3) (p : Fin 6), bit p (goalMask i)=true ↔ p∈triple i := by decide

private lemma all_goals : ∀ a ∈ goals, ∃ i, a=goalMask i := by decide

end PEqualNP.Outside.L_meta_273_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_273_aux

theorem PEqualNP.Outside.L_meta_273 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C,o,bound,ops,valid⟩
  let w := C.gates.foldl step init
  have at_input (p : Fin 6) : w.map (bit p)=C.wires (List.ofFn (fun q : Fin 6 => decide (q=p))) := by
    simpa only [w,Circuit.wires,init_bits] using fold_bits p C.gates init ops
  have output (i : Fin 3) : w.getD (o i) 0=goalMask i := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let p : Fin 6 := ⟨k,hk⟩
    change bit p (w.getD (o i) 0)=bit p (goalMask i)
    rw [←bit_read,at_input]
    apply Bool.eq_iff_iff.mpr
    exact ((valid i).1 p).trans (goal_bits i p).symm
  have done' : goals ⊆ allowed w := by
    intro a ha
    obtain ⟨i,rfl⟩ := all_goals a ha
    exact output i ▸ read_allowed w (o i)
  obtain ⟨sub,cap⟩ := bounds C.gates init
  rw [input_card] at cap
  change C.gates.length ≤ 5 at bound
  exact impossible w sub done' (by change (allowed (C.gates.foldl step init)).card ≤ 12; omega)
    (invariant C.gates init (fun _ h => Or.inl h))
