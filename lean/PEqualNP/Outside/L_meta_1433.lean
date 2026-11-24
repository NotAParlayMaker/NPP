import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1433_aux
open PEqualNP.CircuitLowerBounds
abbrev Word := BitVec 32
def inputA : Word := 0xaaaaaaaa
def inputB : Word := 0xcccccccc
def inputC : Word := 0xf0f0f0f0
def inputD : Word := 0xff00ff00
def inputE : Word := 0xffff0000
def cols : List Word := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def wordOp (op : GateOp) (as : List Word) : Word :=
  match op, as with
  | .and, [] => BitVec.allOnes 32
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, [] => BitVec.allOnes 32
  | .not, a :: _ => ~~~a
  | _, _ => 0

def wordStep (w : List Word) (g : Gate) : Word :=
  wordOp g.op (g.inputs.map fun i => w.getD i 0)

def wordRun (w : List Word) (gs : List Gate) : List Word :=
  gs.foldl (fun ws g => ws ++ [wordStep ws g]) w

def bits (w : List Word) (j : ℕ) : List Bool :=
  w.map (fun a => a.getLsbD j)

lemma bits_get (w : List Word) (j i : ℕ) :
    (bits w j).getD i false = (w.getD i 0).getLsbD j := by
  simpa [bits] using (List.getD_map (l := w) (d := 0) (n := i)
    (fun a : Word => a.getLsbD j))

def Allowed (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

theorem wordOp_bits (op : GateOp) (as : List Word) (j : ℕ) (hj : j < 32)
    (h : Allowed op) (hlen : as.length ≤ 2) :
    (wordOp op as).getLsbD j = op.eval (bits as j) := by
  rcases h with rfl | rfl | rfl <;>
    cases as with
    | nil =>
      simp only [wordOp, GateOp.eval, bits, List.map_nil, List.all_nil,
        List.any_nil, List.headD_nil, BitVec.getLsbD_allOnes,
        hj, decide_true, Bool.not_false]
      all_goals exact BitVec.getLsbD_zero

    | cons a rest =>
      cases rest with
      | nil => simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil,
          List.all_cons, List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil,
          Bool.and_true, Bool.or_false, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
      | cons b tail =>
        have ht : tail = [] := by simpa using hlen
        subst tail
        simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil, List.all_cons,
          List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil, Bool.and_true,
          Bool.or_false, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj,
          decide_true, Bool.true_and]

theorem wordStep_bits (g : Gate) (w : List Word) (j : ℕ) (hj : j < 32)
    (h : Allowed g.op) (hlen : g.inputs.length ≤ 2) :
    (wordStep w g).getLsbD j = g.op.eval (g.inputs.map fun i => (bits w j).getD i false) := by
  rw [wordStep, wordOp_bits _ _ _ hj h (by simpa)]
  simp only [bits, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (bits_get w j i).symm

theorem wordRun_bits (gs : List Gate) (ws : List Word) (j : ℕ) (hj : j < 32)
    (hok : ∀ g ∈ gs, Allowed g.op ∧ g.inputs.length ≤ 2) :
    bits (wordRun ws gs) j =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (bits ws j) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change bits (wordRun (ws ++ [wordStep ws g]) gs) j = _
    rw [ih _ (fun g hg => hok g (List.mem_cons_of_mem _ hg))]
    simp only [List.foldl_cons]
    congr 1
    have hg := hok g List.mem_cons_self
    unfold bits
    rw [List.map_append]
    exact congrArg (fun a => (ws.map (fun b => b.getLsbD j)) ++ [a])
      (wordStep_bits g ws j hj hg.1 hg.2)


def row (j : ℕ) (i : Fin 5) := (cols.getD i.val 0).getLsbD j
def tt (T : ℕ) (x : Fin 5 → Bool) := Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

theorem index_row : ∀ i : Fin 32, (∑ j : Fin 5, if row i.val j then 2 ^ (j : ℕ) else 0) = i.val := by
  decide +kernel

theorem realization (T : ℕ) (gs : List Gate) (out : ℕ)
    (legal : ∀ g ∈ gs, Allowed g.op ∧ g.inputs.length ≤ 2)
    (ev : ∀ x, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = tt T x) :
    (wordRun cols gs).getD out 0 = BitVec.ofNat 32 T := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [← bits_get,wordRun_bits _ _ _ hj legal]
  have eq : bits cols j = List.ofFn (row j) := by rfl
  rw [eq]
  change Circuit.eval ⟨gs,out⟩ _ = _
  rw [ev,tt,index_row ⟨j,hj⟩]
  rw [BitVec.getLsbD_ofNat]
  simp [hj]

-- A state records the available truth tables and the remaining binary and unary gates.
def produces (neg : Bool) (w : Finset Word) (z : Word) : Prop :=
  if neg then ∃ a ∈ w, z = ~~~a else ∃ a ∈ w, ∃ b ∈ w, z = a &&& b ∨ z = a ||| b

def cost (neg : Bool) : ℕ := if neg then 0 else 1
def invCost (neg : Bool) : ℕ := if neg then 1 else 0

inductive Reach : Finset Word → ℕ → ℕ → Word → Prop where
  | hit {w k d t} (mem : t ∈ w) : Reach w k d t
  | add {w k d t z l e} (neg : Bool) (fresh : z ∉ w) (nz : z ≠ 0) (no : z ≠ BitVec.allOnes 32)
      (next : produces neg w z) (rest : Reach (insert z w) l e t)
      (hk : l + cost neg ≤ k) (hd : e + invCost neg ≤ d) : Reach w k d t

theorem increase {w k d t} (h : Reach w k d t) {j e} (le : k ≤ j) (de : d ≤ e) : Reach w j e t := by
  cases h with
  | hit m => exact .hit m
  | add n f a b next rest hk hd => exact .add n f a b next rest (hk.trans le) (hd.trans de)

theorem prod_subset {w v : Finset Word} {neg z} (inc : w ⊆ v) (h : produces neg w z) : produces neg v z := by
  cases neg
  · obtain ⟨a,ha,b,hb,h⟩ := h; exact ⟨a,inc ha,b,inc hb,h⟩
  · obtain ⟨a,ha,h⟩ := h; exact ⟨a,inc ha,h⟩

theorem widen {w k d t} (h : Reach w k d t) {v : Finset Word} (sub : w ⊆ v) : Reach v k d t := by
  induction h generalizing v with
  | hit m => exact .hit (sub m)
  | @add w k d t z l e n f nz no prod rest hk hd ih =>
    by_cases hz : z ∈ v
    · apply increase (ih (Finset.insert_subset hz sub)) (by omega) (by omega)
    · exact .add n hz nz no (prod_subset sub prod) (ih (Finset.insert_subset_insert z sub)) hk hd

-- A circuit with k binary gates needs at most k+1 of the available wires.
theorem support {w k d t} (h : Reach w k d t) : ∃ a ⊆ w, a.card ≤ k+1 ∧ Reach a k d t := by
  induction h with
  | hit m => exact ⟨{_},Finset.singleton_subset_iff.mpr m,by simp,.hit (Finset.mem_singleton_self _)⟩
  | @add w k d t z l e n f nz no prod rest hk hd ih =>
    obtain ⟨a,sub,sz,ra⟩ := ih
    by_cases hz : z ∈ a
    · have small : ∃ p ⊆ w, p.card ≤ cost n + 1 ∧ produces n p z := by
        cases n
        · obtain ⟨i,hi,j,hj,op⟩ := prod
          exact ⟨{i,j},Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj),
            by simpa [cost] using Finset.card_le_two,⟨i,by simp,j,by simp,op⟩⟩
        · obtain ⟨i,hi,op⟩ := prod
          exact ⟨{i},Finset.singleton_subset_iff.mpr hi,by simp [cost],⟨i,by simp,op⟩⟩
      obtain ⟨p,pw,pc,pp⟩ := small
      let v := a.erase z ∪ p
      have vw : v ⊆ w := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi|hi
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hi
          exact (Finset.mem_insert.mp (sub mem)).resolve_left ne
        · exact pw hi
      have av : a ⊆ insert z v := by
        intro i hi
        by_cases eq : i=z
        · simp [eq]
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩))
      have card := Finset.card_union_le (s := a.erase z) (t := p)
      rw [Finset.card_erase_of_mem hz] at card
      exact ⟨v,vw,by dsimp [v]; have := a.card_pos.mpr ⟨_,hz⟩; omega,
        .add n (fun mem => f (vw mem)) nz no (prod_subset Finset.subset_union_right pp) (widen ra av) hk hd⟩
    · have aw : a ⊆ w := fun i hi => (Finset.mem_insert.mp (sub hi)).resolve_left (by rintro rfl; exact hz hi)
      exact ⟨a,aw,by omega,increase ra (by omega) (by omega)⟩

def known (w : Finset Word) (z : Word) := z = 0 ∨ z = BitVec.allOnes 32 ∨ z ∈ w
def isInv (o : GateOp) : Bool := match o with | .not => true | _ => false

theorem step_known (w : Finset Word) (g : Gate) (ws : List Word) (ok : Allowed g.op)
    (bank : ∀ i, known w (ws.getD i 0)) :
    known w (wordStep ws g) ∨ produces (isInv g.op) w (wordStep ws g) := by
  obtain ⟨op,ins⟩ := g
  rcases ok with h|h|h <;> simp only at h <;> subst op
  · cases ins with
    | nil => exact Or.inl (Or.inr (Or.inl rfl))
    | cons i is =>
      cases is with
      | nil => exact Or.inl (bank i)
      | cons j js =>
        change known w (ws.getD i 0 &&& ws.getD j 0) ∨ _
        rcases bank i with a|a|a
        · left; rw [a]; first | exact Or.inr (Or.inl (BitVec.allOnes_or)) | simp [known]
        · left; rw [a]; first | exact BitVec.allOnes_and ▸ bank j | simpa using bank j
        · rcases bank j with b|b|b
          · left; rw [b]; first | exact Or.inr (Or.inl (BitVec.or_allOnes)) | simp [known]
          · left; rw [b]; first | exact BitVec.and_allOnes ▸ bank i | simpa using bank i
          · exact Or.inr ⟨_,a,_,b,Or.inl rfl⟩
  · cases ins with
    | nil => exact Or.inl (Or.inl rfl)
    | cons i is =>
      cases is with
      | nil => exact Or.inl (bank i)
      | cons j js =>
        change known w (ws.getD i 0 ||| ws.getD j 0) ∨ _
        rcases bank i with a|a|a
        · left; rw [a]; first | exact BitVec.allOnes_and ▸ bank j | simpa using bank j
        · left; rw [a]; first | exact Or.inr (Or.inl (BitVec.allOnes_or)) | simp [known]
        · rcases bank j with b|b|b
          · left; rw [b]; first | exact BitVec.and_allOnes ▸ bank i | simpa using bank i
          · left; rw [b]; first | exact Or.inr (Or.inl (BitVec.or_allOnes)) | simp [known]
          · exact Or.inr ⟨_,a,_,b,Or.inr rfl⟩
  · cases ins with
    | nil => exact Or.inl (Or.inr (Or.inl rfl))
    | cons i is =>
      change known w (~~~(ws.getD i 0)) ∨ _
      rcases bank i with a|a|a
      · left; rw [a]; first | exact Or.inr (Or.inl (BitVec.allOnes_or)) | simp [known]
      · left; rw [a]; first | exact Or.inr (Or.inl (BitVec.allOnes_or)) | simp [known]
      · exact Or.inr ⟨_,a,rfl⟩

def negatives (gs : List Gate) := gs.countP (fun g => isInv g.op)
def binaries (gs : List Gate) := gs.countP (fun g => !(isInv g.op))

theorem compiled {t : Word} (nz : t ≠ 0) (no : t ≠ BitVec.allOnes 32)
    (gs : List Gate) (ws : List Word) (w : Finset Word) (out : ℕ)
    (legal : ∀ g ∈ gs, Allowed g.op) (bank : ∀ i, known w (ws.getD i 0))
    (result : (wordRun ws gs).getD out 0 = t) : Reach w (binaries gs) (negatives gs) t := by
  induction gs generalizing ws w with
  | nil =>
    have h := bank out
    change ws.getD out 0 = t at result
    rw [result] at h
    exact .hit ((h.resolve_left nz).resolve_left no)
  | cons g gs ih =>
    let z := wordStep ws g
    let n := isInv g.op
    have l : binaries (g::gs) = binaries gs + cost n := by cases h : isInv g.op <;> simp [binaries,List.countP_cons,n,h,cost]
    have d : negatives (g::gs) = negatives gs + invCost n := by cases h : isInv g.op <;> simp [negatives,List.countP_cons,n,h,invCost]
    have update (v : Finset Word) (vw : w ⊆ v) (hz : known v z) :
        ∀ i, known v ((ws++[z]).getD i 0) := by
      intro i
      by_cases lt : i < ws.length
      · rw [List.getD_append _ _ _ _ lt]
        exact (bank i).imp_right (Or.imp_right (fun hm => vw hm))
      · by_cases eq : i=ws.length
        · simpa [eq] using hz
        · rw [List.getD_eq_default _ _ (by simp; omega)]
          exact Or.inl rfl
    have aux (v : Finset Word) (vw : w ⊆ v) (hz : known v z) : Reach v (binaries gs) (negatives gs) t :=
      ih _ _ (fun a ha => legal _ (List.mem_cons_of_mem _ ha)) (update v vw hz) result
    rw [l,d]
    by_cases prev : known w z
    · exact increase (aux w (fun _ h => h) prev) (by omega) (by omega)
    · have prod := (step_known w g ws (legal _ List.mem_cons_self) bank).resolve_left prev
      exact .add n (fun h => prev (Or.inr (Or.inr h))) (fun h => prev (Or.inl h))
        (fun h => prev (Or.inr (Or.inl h))) prod
        (aux (insert z w) (Finset.subset_insert _ _) (Or.inr (Or.inr (Finset.mem_insert_self _ _)))) le_rfl le_rfl


def relation (d : ℕ) (i j : Fin 32) (w : Word) :=
  if d = 0 then (w.getLsbD i.val = true → w.getLsbD j.val = true)
  else w.getLsbD i.val = w.getLsbD j.val

theorem relation_le {d e : ℕ} {i j : Fin 32} {w : Word} (h : relation d i j w) (le : e ≤ d) :
    relation e i j w := by
  unfold relation at *
  split_ifs at * with a b <;> simp_all

theorem reach_relation {w k d t} (h : Reach w k d t) (i j : Fin 32) :
    (∀ a ∈ w, relation d i j a) → relation d i j t := by
  induction h generalizing i j with
  | hit m => exact fun all => all _ m
  | @add w k d t z l e n fresh nz no pr rest hk hd ih =>
    intro all
    have hz : relation d i j z := by
      cases n
      · obtain ⟨a,ha,b,hb,eq|eq⟩ := pr
        all_goals
          have h1 := all a ha
          have h2 := all b hb
          subst z
          unfold relation at *
          split_ifs at * <;> simp_all [BitVec.getLsbD_and,BitVec.getLsbD_or,Bool.and_eq_true,Bool.or_eq_true]
          all_goals grind
      · obtain ⟨a,ha,eq⟩ := pr
        have h1 := all a ha
        have pos : d ≠ 0 := by simp [invCost] at hd; omega
        simp_all [relation,BitVec.getLsbD_not]
    have child : relation e i j t := ih i j (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl|mem
      · exact relation_le hz (by omega)
      · exact relation_le (all a mem) (by omega))
    by_cases ed : e=0 ∧ d ≠ 0
    · have same (a : Word) (hm : a ∈ insert z w) : relation d j i a := by
        have rel : relation d i j a := (Finset.mem_insert.mp hm).elim (fun h => h ▸ hz) (all a)
        simpa [relation,ed.2,eq_comm] using rel
      have rev : relation e j i t := ih j i (fun a ha => relation_le (same a ha) (by omega))
      rw [relation,ite_eq_right ed.2]
      rw [relation,ite_eq_left ed.1] at child rev
      exact Bool.eq_iff_iff.mpr ⟨child,rev⟩
    · unfold relation at *
      split_ifs at * <;> simp_all

def candidates (neg : Bool) (w : List Word) : List Word :=
  let raw := if neg then w.map (fun a => ~~~a)
      else w.flatMap fun a => w.flatMap fun b => [a &&& b,a ||| b]
  raw.eraseDups.filter (fun z => !(w.contains z) && z != 0 && z != BitVec.allOnes 32)

theorem candidate_ok {w : List Word} {n z} (p : produces n w.toFinset z)
    (fresh : z ∉ w.toFinset) (nz : z ≠ 0) (no : z ≠ BitVec.allOnes 32) : z ∈ candidates n w := by
  simp only [candidates,List.mem_filter,List.mem_eraseDups]
  refine ⟨?_,by simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne]; exact ⟨⟨(by simpa using List.mem_toFinset.not.mp fresh),nz⟩,no⟩⟩
  cases n
  · obtain ⟨a,ha,b,hb,eq|eq⟩ := p
    all_goals simp only [Bool.false_eq_true,ite_false,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
    · exact ⟨a,List.mem_toFinset.mp ha,b,List.mem_toFinset.mp hb,Or.inl eq⟩
    · exact ⟨a,List.mem_toFinset.mp ha,b,List.mem_toFinset.mp hb,Or.inr eq⟩
  · obtain ⟨a,ha,eq⟩ := p
    exact List.mem_map.mpr ⟨a,List.mem_toFinset.mp ha,eq.symm⟩

theorem shrink {w : List Word} {k d t} (nd : w.Nodup) (h : Reach w.toFinset k d t) :
    ∃ u ∈ w.sublistsLen (min (k+1) w.length), u.Nodup ∧ Reach u.toFinset k d t := by
  obtain ⟨a,aw,hs,ha⟩ := support h
  let size := min (k+1) w.length
  have le : a.card ≤ size := le_min hs ((Finset.card_le_card aw).trans_eq (List.toFinset_card_of_nodup nd))
  have bound : size ≤ w.toFinset.card := by rw [List.toFinset_card_of_nodup nd]; exact min_le_right _ _
  obtain ⟨v,av,vw,sz⟩ := Finset.exists_subsuperset_card_eq aw le bound
  let u := w.filter (fun a => a ∈ v)
  have sub : List.Sublist u w := List.filter_sublist
  have eq : u.toFinset = v := by
    ext a
    simp only [u,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun m => ⟨List.mem_toFinset.mp (vw m),m⟩⟩
  have du := sub.nodup nd
  have len : u.length = size := by rw [←List.toFinset_card_of_nodup du,eq,sz]
  have r : Reach u.toFinset k d t := eq ▸ widen ha av
  exact ⟨u,List.mem_sublistsLen.mpr ⟨sub,len⟩,du,r⟩

def permWord (p : Fin 32 → Fin 32) (w : Word) : Word := BitVec.ofBoolListLE
  (List.ofFn (fun i : Fin 32 => w.getLsbD (p i).val)) |>.setWidth 32

theorem perm_bit (p : Fin 32 → Fin 32) (w : Word) (i : Fin 32) :
    (permWord p w).getLsbD i.val = w.getLsbD (p i).val := by
  rw [permWord,BitVec.getLsbD_setWidth,BitVec.getLsbD_ofBoolListLE]
  simp only [i.isLt,decide_true,Bool.true_and]
  rw [List.getD_eq_getElem _ _ (by simp)]
  exact List.getElem_ofFn ..

def ren (p : Fin 32 → Fin 32) (w : List Word) := w.map (permWord p)

theorem perm_laws (p : Fin 32 → Fin 32) (a b : Word) :
    permWord p (a &&& b) = permWord p a &&& permWord p b ∧
    permWord p (a ||| b) = permWord p a ||| permWord p b ∧
    permWord p (~~~a) = ~~~(permWord p a) ∧ permWord p 0 = 0 ∧
    permWord p (BitVec.allOnes 32) = BitVec.allOnes 32 := by
  repeat' constructor
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i hi
  all_goals simp only [perm_bit p _ ⟨i,hi⟩,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
    BitVec.getLsbD_zero,BitVec.getLsbD_allOnes,hi,(p ⟨i,hi⟩).isLt]
  all_goals exact (BitVec.getLsbD_zero).trans BitVec.getLsbD_zero.symm

theorem perm_reach {w k d t} (h : Reach w k d t) (p : Fin 32 → Fin 32) (inj : Function.Surjective p) :
    Reach (w.image (permWord p)) k d (permWord p t) := by
  have pinj : Function.Injective (permWord p) := by
    intro a b eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨j,hj⟩ := inj ⟨i,hi⟩
    have en := congrArg (fun z : Word => z.getLsbD j.val) eq
    simp only [perm_bit,hj] at en
    exact en
  induction h with
  | hit hm => exact .hit (Finset.mem_image_of_mem _ hm)
  | @add w k d t z l e n fresh nz no pr rest hk hd ih =>
    have laws := perm_laws p z z
    have ne : permWord p z ∉ w.image (permWord p) := by
      intro hm
      obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp hm
      exact fresh (pinj eq ▸ ha)
    refine .add n ne (fun eq => nz (pinj (eq.trans laws.2.2.2.1.symm)))
        (fun eq => no (pinj (eq.trans laws.2.2.2.2.symm))) ?_ (by simpa using ih) hk hd
    cases n
    · obtain ⟨a,ha,b,hb,eq|eq⟩ := pr
      · exact ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,Or.inl (eq ▸ (perm_laws p a b).1)⟩
      · exact ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,Or.inr (eq ▸ (perm_laws p a b).2.1)⟩
    · obtain ⟨a,ha,eq⟩ := pr
      exact ⟨_,Finset.mem_image_of_mem _ ha,eq ▸ (perm_laws p a a).2.2.1⟩


def correct (children : Array (List Word)) (k d : ℕ) (t : Word) :=
  ∀ q (hq : q < children.size), ¬ Reach children[q].toFinset k d t



-- Bit 32*i+j represents the ordered pair of input rows i and j.
def packedRows (f : ℕ → Word) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, a => 2^32 * packedRows f n (a+1) + (f a).toNat

theorem packedRows_bit (f : ℕ → Word) (n a i j : ℕ) (hi : i < n) (hj : j < 32) :
    (packedRows f n a).testBit (32*i+j) = (f (a+i)).getLsbD j := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    rw [packedRows,Nat.testBit_two_pow_mul_add _ (f a).isLt]
    cases i with
    | zero => simp [hj,BitVec.getLsbD]
    | succ i =>
      rw [if_neg (by omega),show 32*(i+1)+j-32=32*i+j by omega,ih _ _ (by omega)]
      congr 2
      omega

theorem packedRows_bound (f : ℕ → Word) (n a : ℕ) : packedRows f n a < 2^(32*n) := by
  induction n generalizing a with
  | zero => simp [packedRows]
  | succ n ih =>
    rw [packedRows, Nat.mul_succ, pow_add]
    have h := ih (a+1)
    have h' := (f a).isLt
    omega

def targetPairs (t : Word) := packedRows (fun i => if t.getLsbD i then ~~~t else 0) 32 0

def wirePairs (d : ℕ) (w : Word) := packedRows (fun i =>
  if w.getLsbD i then w else if d = 0 then BitVec.allOnes 32 else ~~~w) 32 0

theorem targetPairs_bit (t : Word) (i j : Fin 32) :
    (targetPairs t).testBit (32*i.val+j.val) = true ↔
      t.getLsbD i.val = true ∧ t.getLsbD j.val = false := by
  rw [targetPairs,packedRows_bit _ _ _ _ _ i.isLt j.isLt]
  simp only [Nat.zero_add]
  cases h : t.getLsbD i.val <;> simp [h,BitVec.getLsbD_not,j.isLt]

theorem wirePairs_bit (d : ℕ) (w : Word) (i j : Fin 32) :
    (wirePairs d w).testBit (32*i.val+j.val) = true ↔ relation d i j w := by
  rw [wirePairs,packedRows_bit _ _ _ _ _ i.isLt j.isLt]
  simp only [Nat.zero_add]
  unfold relation
  cases h : w.getLsbD i.val <;> by_cases e : d=0 <;>
    simp only [e,ite_true,ite_false,Bool.false_eq_true,BitVec.getLsbD_allOnes,
      BitVec.getLsbD_not,j.isLt,decide_true,Bool.true_and,Bool.not_eq_true'] <;>
    cases w.getLsbD j.val <;> decide

def joined (d : ℕ) (acc : ℕ) (xs : List Word) := xs.foldl (fun b w => b &&& wirePairs d w) acc

theorem joined_bit (d acc i : ℕ) (xs : List Word) :
    (joined d acc xs).testBit i = true ↔ acc.testBit i = true ∧
      ∀ w ∈ xs, (wirePairs d w).testBit i = true := by
  induction xs generalizing acc with
  | nil => simp [joined]
  | cons w ws ih =>
    change (joined d (acc &&& wirePairs d w) ws).testBit i = true ↔ _
    rw [ih]
    simp [and_assoc]

theorem obstructed {d k t} {xs : List Word}
    (h : joined d (targetPairs t) xs ≠ 0) : ¬ Reach xs.toFinset k d t := by
  intro r
  obtain ⟨v,hv⟩ : ∃ v, (joined d (targetPairs t) xs).testBit v = true := by
    by_contra! hh
    exact h (Nat.eq_of_testBit_eq (by simpa using hh))
  obtain ⟨ht,ha⟩ := (joined_bit ..).mp hv
  have bound : v < 1024 := by
    by_contra! le
    have lt := packedRows_bound (fun i => if t.getLsbD i then ~~~t else 0) 32 0
    have bad := Nat.testBit_lt_two_pow (lt_of_lt_of_le lt (Nat.pow_le_pow_right (by decide) le))
    change (targetPairs t).testBit v = false at bad
    exact Bool.noConfusion (bad.symm.trans ht)
  let i : Fin 32 := ⟨v/32,by omega⟩
  let j : Fin 32 := ⟨v % 32,by omega⟩
  have eq : v = 32*i.val+j.val := by dsimp [i,j]; omega
  rw [eq] at ht ha
  obtain ⟨p,n⟩ := (targetPairs_bit t i j).mp ht
  have rel := reach_relation r i j (fun a hm => (wirePairs_bit ..).mp (ha a (List.mem_toFinset.mp hm)))
  unfold relation at rel
  split at rel <;> simp_all


def labelled (d : ℕ) (w : Word) := (w,wirePairs d w)

def remains (t : Word) (u : List (Word × ℕ)) :=
  u.foldl (fun m a => m &&& a.2) (targetPairs t)

theorem fold_labels (d m : ℕ) (u : List Word) :
    (u.map (labelled d)).foldl (fun b a => b &&& a.2) m = joined d m u := by
  induction u generalizing m with
  | nil => rfl
  | cons a u ih => exact ih _

-- A nonzero intersection supplies a pair the selected wires cannot distinguish.
-- When the intersection is empty, the next packed index names a previously checked bank.
def refsOk (t : Word) (children : Array (List Word)) : List (List (Word × ℕ)) → ℕ → Bool
  | [], _ => true
  | u::us, v =>
    if remains t u != 0 then refsOk t children us v
    else
      let q := v % 2048
      q < children.size && u.all (fun a => (children[q]?.getD []).contains a.1) && refsOk t children us (v / 2048)

theorem refs_ok {t d k c us v} (good : correct c k d t) (h : refsOk t c us v = true) :
    ∀ u : List Word, u.map (labelled d) ∈ us → ¬ Reach u.toFinset k d t := by
  induction us generalizing v with
  | nil => simp
  | cons head us ih =>
    intro u hu
    simp only [refsOk] at h
    split at h
    next bad =>
      rcases List.mem_cons.mp hu with eq|tail
      · subst head
        apply obstructed
        simpa only [remains,fold_labels,bne_iff_ne] using bad
      · exact ih h u tail
    next _ =>
      obtain ⟨⟨bound,inc⟩,tail⟩ := Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp
      rcases List.mem_cons.mp hu with eq|mem
      · subst head
        have lt : v % 2048 < c.size := of_decide_eq_true bound
        intro r
        apply good _ lt
        apply widen r
        intro a ha
        have z := List.all_eq_true.mp inc (labelled d a) (List.mem_map_of_mem (List.mem_toFinset.mp ha))
        simpa [labelled,Array.getElem?_eq_getElem lt] using z
      · exact ih tail u mem

def fastNext (t : Word) (k d : ℕ) (c : Array (List Word)) (w : List Word) : List Word → List ℕ → Bool
  | [], _ => true
  | _::_, [] => false
  | z::zs, data::ds =>
    let added := z::w
    refsOk t c ((added.map (labelled d)).sublistsLen (min (k+1) added.length)) data &&
      fastNext t k d c w zs ds

theorem fast_next_ok {t k d c w zs data} (good : correct c k d t)
    (h : fastNext t k d c w zs data = true) :
    ∀ z ∈ zs, (z::w).Nodup → ¬ Reach (z::w).toFinset k d t := by
  induction zs generalizing data with
  | nil => simp
  | cons a as ih =>
    cases data with
    | nil => simp [fastNext] at h
    | cons v vs =>
      obtain ⟨one,tail⟩ := Bool.and_eq_true_iff.mp h
      intro z hz nd re
      rcases List.mem_cons.mp hz with rfl|hz
      · obtain ⟨u,hu,_,ru⟩ := shrink nd re
        obtain ⟨sub,len⟩ := List.mem_sublistsLen.mp hu
        exact refs_ok good one u (List.mem_sublistsLen.mpr ⟨sub.map _,by simpa using len⟩) ru
      · exact ih tail z hz nd re

def certState (t : Word) (k d : ℕ) (w : List Word) (bin inv : Array (List Word))
    (cb ci : List ℕ) :=
  decide w.Nodup && !(w.contains t) &&
    (k == 0 || fastNext t (k-1) d bin w (candidates false w) cb) &&
    (d == 0 || fastNext t k (d-1) inv w (candidates true w) ci)

theorem state_ok {t k d w bin inv cb ci}
    (b : correct bin (k-1) d t) (i : correct inv k (d-1) t)
    (h : certState t k d w bin inv cb ci = true) : ¬ Reach w.toFinset k d t := by
  simp only [certState,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,Bool.not_eq_true'] at h
  obtain ⟨⟨⟨nd,miss⟩,bb⟩,ii⟩ := h
  intro reach
  cases reach with
  | hit mem => simpa [List.mem_toFinset.mp mem] using miss
  | add neg fresh nz no prod rest hk hd =>
    have cand := candidate_ok prod fresh nz no
    have nd' := List.nodup_cons.mpr ⟨List.mem_toFinset.not.mp fresh,nd⟩
    cases neg
    · simp [cost,invCost] at hk hd
      exact fast_next_ok b (bb.resolve_left (by omega)) _ cand nd' (by simpa using increase rest (j := k-1) (e := d) (by omega) hd)
    · simp [cost,invCost] at hk hd
      exact fast_next_ok i (ii.resolve_left (by omega)) _ cand nd' (by simpa using increase rest (j := k) (e := d-1) hk (by omega))


theorem noRows (t : Word) (k d : ℕ) : correct #[] k d t := by
  intro q h; simp at h

def part (rows : Array (List Word)) (t : Word) (k d : ℕ) (bin inv : Array (List Word)) :
    ℕ → List (List ℕ × List ℕ) → Bool
  | _, [] => true
  | j, dat::ds =>
    match rows[j]? with
    | none => false
    | some w => certState t k d w bin inv dat.1 dat.2 && part rows t k d bin inv (j+1) ds

theorem part_ok {rows t k d bin inv j data} (hbin : correct bin (k-1) d t)
    (hinv : correct inv k (d-1) t) (good : part rows t k d bin inv j data = true) :
    ∀ q (hq : q < rows.size), j ≤ q → q < j+data.length → ¬ Reach rows[q].toFinset k d t := by
  induction data generalizing j with
  | nil => simp only [List.length_nil,Nat.add_zero]; omega
  | cons item rest ih =>
    intro q hq le lt
    simp only [part] at good
    cases eq : rows[j]? with
    | none => simp [eq] at good
    | some w =>
      rw [eq,Bool.and_eq_true] at good
      by_cases same : j=q
      · subst j
        have key := Option.some.inj ((Array.getElem?_eq_getElem hq).symm.trans eq)
        rw [key]
        exact state_ok hbin hinv good.1
      · apply ih good.2 q hq (by omega)
        simp only [List.length_cons] at lt
        omega



abbrev Shifts := List (ℕ × Word)

def turns (s : ℕ) (i : Fin 32) : Fin 32 :=
  ⟨if i.val < 32-s % 32 then s % 32+i.val else i.val-(32-s % 32),by split <;> omega⟩

theorem turn_bit (w : Word) (s : ℕ) (i : Fin 32) :
    (w.rotateRight s).getLsbD i.val = w.getLsbD (turns s i).val := by
  simp only [BitVec.getLsbD_rotateRight,turns,i.isLt,decide_true,Bool.true_and]
  split <;> rfl

def shiftRow : Shifts → Fin 32 → Fin 32
  | [], i => i
  | (s,m)::ps, i => if m.getLsbD i.val then turns s i else shiftRow ps i

def shiftWord : Shifts → Word → Word
  | [], w => w
  | (s,m)::ps, w => (m &&& w.rotateRight s) ||| ((~~~m) &&& shiftWord ps w)

theorem shift_bit (ps : Shifts) (w : Word) (i : Fin 32) :
    (shiftWord ps w).getLsbD i.val = w.getLsbD (shiftRow ps i).val := by
  induction ps with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨s,m⟩ := x
    simp only [shiftRow,shiftWord,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
      i.isLt,decide_true,Bool.true_and,turn_bit,ih]
    cases m.getLsbD i.val <;> simp

theorem shift_eq (ps : Shifts) (w : Word) : permWord (shiftRow ps) w = shiftWord ps w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (perm_bit _ _ ⟨i,hi⟩).trans (shift_bit _ _ ⟨i,hi⟩).symm

abbrev ShiftMap := Shifts × List ℕ
def goodShift (t : Word) (p : ShiftMap) :=
  shiftWord p.1 t == t && (List.range 32).all (fun i =>
    (shiftRow p.1 ⟨(p.2.getD i 0) % 32,by omega⟩).val == i)

theorem goodShift_ok {t : Word} {p : ShiftMap} (h : goodShift t p = true) :
    Function.Surjective (shiftRow p.1) ∧ permWord (shiftRow p.1) t = t := by
  obtain ⟨eq,all⟩ := Bool.and_eq_true_iff.mp h
  constructor
  · intro i
    exact ⟨_,Fin.ext (beq_iff_eq.mp (List.all_eq_true.mp all i.val (List.mem_range.mpr i.isLt)))⟩
  · exact (shift_eq _ _).trans (beq_iff_eq.mp eq)

-- Permutations of the five inputs preserve the majority truth table.
def aliasPart (raw reps : Array (List Word)) (t : Word) (maps : Array ShiftMap) :
    ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | j,(idx,pi)::ds =>
    match raw[j]?,reps[idx]?,maps[pi]? with
    | some u,some v,some p => u.all (fun x => v.contains (shiftWord p.1 x)) &&
                              aliasPart raw reps t maps (j+1) ds
    | _,_,_ => false

def validMaps (maps : Array ShiftMap) (t : Word) := ∀ p ∈ maps,
    Function.Surjective (shiftRow p.1) ∧ permWord (shiftRow p.1) t = t

theorem alias_ok {raw reps t maps j data k d} (valid : validMaps maps t)
    (good : correct reps k d t) (checks : aliasPart raw reps t maps j data = true) :
    ∀ q (hq : q < raw.size), j ≤ q → q < j+data.length → ¬ Reach raw[q].toFinset k d t := by
  induction data generalizing j with
  | nil => simp only [List.length_nil,Nat.add_zero]; omega
  | cons item ds ih =>
    obtain ⟨idx,pi⟩ := item
    intro q hq le lt
    simp only [aliasPart] at checks
    split at checks
    next u v p hu hv hp =>
      rw [Bool.and_eq_true] at checks
      by_cases eq : j=q
      · subst j
        have rawEq := Option.some.inj ((Array.getElem?_eq_getElem hq).symm.trans hu)
        obtain ⟨ri,rfl⟩ := Array.getElem?_eq_some_iff.mp hv
        obtain ⟨mi,rfl⟩ := Array.getElem?_eq_some_iff.mp hp
        obtain ⟨bij,keep⟩ := valid _ (Array.getElem_mem mi)
        intro reach
        rw [rawEq] at reach
        have mapped := perm_reach reach _ bij
        rw [keep] at mapped
        apply good idx ri
        apply widen mapped
        intro a ha
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
        exact List.mem_toFinset.mpr (by simpa [shift_eq] using List.all_eq_true.mp checks.1 z (List.mem_toFinset.mp hz))
      · apply ih checks.2 q hq (by omega)
        simp only [List.length_cons] at lt
        omega
    next => contradiction

def legal (gs : List Gate) := ∀ g ∈ gs, Allowed g.op ∧ g.inputs.length ≤ 2
def mono (gs : List Gate) := ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

theorem countBudget (gs : List Gate) :
    binaries gs + negatives gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases e : isInv g.op <;> simp [binaries,negatives,List.countP_cons,e] at * <;> omega

theorem small_impossible {T : ℕ} {k : ℕ} (nz : BitVec.ofNat 32 T ≠ 0)
    (no : BitVec.ofNat 32 T ≠ BitVec.allOnes 32) (lb : ¬ Reach cols.toFinset k 1 (BitVec.ofNat 32 T))
    (gs : List Gate) (out : ℕ) (legal : legal gs)
    (one : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i=j)
    (uses : ∃ i : Fin gs.length, (gs.get i).op = .not)
    (ev : ∀ x, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = tt T x) : k+2 ≤ gs.length := by
  classical
  obtain ⟨i,hi⟩ := uses
  have iso (j : Fin gs.length) : isInv (gs.get j).op = true ↔ j=i := by
    constructor
    · intro h
      apply one _ _ _ hi
      cases e : (gs.get j).op <;> simp_all [isInv]
    · intro eq; subst j; rw [hi]; rfl
  have cnt : negatives gs = 1 := by
    change gs.countP _ = 1
    rw [← List.ofFn_get gs,List.countP_ofFn]
    have hs : (Finset.univ.filter fun j : Fin gs.length => isInv (gs.get j).op = true) = {i} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      exact iso j
    rw [hs]
    simp
  have total := countBudget gs
  by_contra! bad
  apply lb
  apply increase (compiled nz no gs cols cols.toFinset out (fun g hg => (legal g hg).1) _ (realization T gs out legal ev)) (by omega) (by omega)
  intro j
  by_cases lt : j < cols.length
  · rw [List.getD_eq_getElem _ _ lt]
    exact Or.inr (Or.inr (List.mem_toFinset.mpr (List.getElem_mem lt)))
  · exact Or.inl (List.getD_eq_default _ _ (by omega))

def Verdict (T : ℕ) := ∀ (gs : List Gate) (out : ℕ), legal gs →
    (∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i=j) →
    (∀ x, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = tt T x) →
    ∃ (hs : List Gate) (o : ℕ), mono hs ∧ hs.length ≤ gs.length ∧
      ∀ x, Circuit.eval ⟨hs,o⟩ (List.ofFn x) = tt T x

theorem verdict {T k : ℕ} (nz : BitVec.ofNat 32 T ≠ 0) (no : BitVec.ofNat 32 T ≠ BitVec.allOnes 32)
    (lb : ¬ Reach cols.toFinset k 1 (BitVec.ofNat 32 T)) (hs : List Gate) (o : ℕ)
    (hm : mono hs) (sz : hs.length ≤ k+2) (ev : ∀ x, Circuit.eval ⟨hs,o⟩ (List.ofFn x) = tt T x) : Verdict T := by
  intro gs out lg one orig
  by_cases uses : ∃ i : Fin gs.length, (gs.get i).op = .not
  · exact ⟨hs,o,hm,sz.trans (small_impossible nz no lb gs out lg one uses orig),ev⟩
  · refine ⟨gs,out,?_,le_rfl,orig⟩
    intro g hg
    obtain ⟨op,len⟩ := lg g hg
    obtain ⟨j,eq⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨hj,rfl⟩ := List.getElem?_eq_some_iff.mp eq
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun no => (uses ⟨⟨j,hj⟩,no⟩).elim)),len⟩

def x0s2d0 : Array (List Word) := #[[inputA,0xc0c0c0c0,0xffffff00]]
def x0s2d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s2d0g0 : ∀ q (hq : q < x0s2d0.size), 0 ≤ q → q < 1 → ¬ Reach x0s2d0[q].toFinset 2 0 0xeaeaea80 := by
  have check : part x0s2d0 0xeaeaea80 2 0 #[] #[] 0 x0s2d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s2d0ok : correct x0s2d0 2 0 0xeaeaea80 := by
  exact fun q hq => x0s2d0g0 q hq (Nat.zero_le _) hq
def x0s2d1 : Array (List Word) := #[[inputA,0xc0c0c0c0,0xffffff00]]
def x0s2d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s2d1g0 : ∀ q (hq : q < x0s2d1.size), 0 ≤ q → q < 1 → ¬ Reach x0s2d1[q].toFinset 2 1 0xeaeaea80 := by
  have check : part x0s2d1 0xeaeaea80 2 1 #[] x0s2d0 0 x0s2d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x0s2d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s2d1ok : correct x0s2d1 2 1 0xeaeaea80 := by
  exact fun q hq => x0s2d1g0 q hq (Nat.zero_le _) hq
def x0s3d0 : Array (List Word) := #[[inputA,0xc0c0c0c0,inputD,inputE],[inputA,inputB,inputC,0xffffff00]]
def x0s3d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s3d0g0 : ∀ q (hq : q < x0s3d0.size), 0 ≤ q → q < 2 → ¬ Reach x0s3d0[q].toFinset 3 0 0xeaeaea80 := by
  have check : part x0s3d0 0xeaeaea80 3 0 x0s2d0 #[] 0 x0s3d0g0c = true := by decide +kernel
  exact part_ok x0s2d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s3d0ok : correct x0s3d0 3 0 0xeaeaea80 := by
  exact fun q hq => x0s3d0g0 q hq (Nat.zero_le _) hq
def x0s3d1 : Array (List Word) := #[[inputA,0xc0c0c0c0,inputD,inputE],[inputA,inputB,inputC,0xffffff00]]
def x0s3d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0]),([0,0,0,0,0,0,0,0,0,0,0,0],[1,1,1,1])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s3d1g0 : ∀ q (hq : q < x0s3d1.size), 0 ≤ q → q < 2 → ¬ Reach x0s3d1[q].toFinset 3 1 0xeaeaea80 := by
  have check : part x0s3d1 0xeaeaea80 3 1 x0s2d1 x0s3d0 0 x0s3d1g0c = true := by decide +kernel
  exact part_ok x0s2d1ok x0s3d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s3d1ok : correct x0s3d1 3 1 0xeaeaea80 := by
  exact fun q hq => x0s3d1g0 q hq (Nat.zero_le _) hq
def x0s4d0 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x0s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s4d0g0 : ∀ q (hq : q < x0s4d0.size), 0 ≤ q → q < 1 → ¬ Reach x0s4d0[q].toFinset 4 0 0xeaeaea80 := by
  have check : part x0s4d0 0xeaeaea80 4 0 x0s3d0 #[] 0 x0s4d0g0c = true := by decide +kernel
  exact part_ok x0s3d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s4d0ok : correct x0s4d0 4 0 0xeaeaea80 := by
  exact fun q hq => x0s4d0g0 q hq (Nat.zero_le _) hq
def x0s4d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x0s4d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s4d1g0 : ∀ q (hq : q < x0s4d1.size), 0 ≤ q → q < 1 → ¬ Reach x0s4d1[q].toFinset 4 1 0xeaeaea80 := by
  have check : part x0s4d1 0xeaeaea80 4 1 x0s3d1 x0s4d0 0 x0s4d1g0c = true := by decide +kernel
  exact part_ok x0s3d1ok x0s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x0s4d1ok : correct x0s4d1 4 1 0xeaeaea80 := by
  exact fun q hq => x0s4d1g0 q hq (Nat.zero_le _) hq
def x0gates : List Gate := [⟨.and, [1,2]⟩,⟨.or, [3,4]⟩,⟨.or, [5,6]⟩,⟨.and, [5,6]⟩,⟨.or, [0,8]⟩,⟨.and, [7,9]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result0 : Verdict 0xeaeaea80 := by
  apply verdict (k := 4) (by decide) (by decide) (x0s4d1ok 0 (by decide)) x0gates 10
  · simp [x0gates,mono]
  · decide
  · decide +kernel

def x1s4d0 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x1s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x1s4d0g0 : ∀ q (hq : q < x1s4d0.size), 0 ≤ q → q < 1 → ¬ Reach x1s4d0[q].toFinset 4 0 0xeee0e8e0 := by
  have check : part x1s4d0 0xeee0e8e0 4 0 #[] #[] 0 x1s4d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x1s4d0ok : correct x1s4d0 4 0 0xeee0e8e0 := by
  exact fun q hq => x1s4d0g0 q hq (Nat.zero_le _) hq
def x1s4d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x1s4d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x1s4d1g0 : ∀ q (hq : q < x1s4d1.size), 0 ≤ q → q < 1 → ¬ Reach x1s4d1[q].toFinset 4 1 0xeee0e8e0 := by
  have check : part x1s4d1 0xeee0e8e0 4 1 #[] x1s4d0 0 x1s4d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x1s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x1s4d1ok : correct x1s4d1 4 1 0xeee0e8e0 := by
  exact fun q hq => x1s4d1g0 q hq (Nat.zero_le _) hq
def x1gates : List Gate := [⟨.and, [0,1]⟩,⟨.or, [0,1]⟩,⟨.or, [4,5]⟩,⟨.and, [3,7]⟩,⟨.or, [2,8]⟩,⟨.and, [6,9]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result1 : Verdict 0xeee0e8e0 := by
  apply verdict (k := 4) (by decide) (by decide) (x1s4d1ok 0 (by decide)) x1gates 10
  · simp [x1gates,mono]
  · decide
  · decide +kernel

def x2s4d0 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x2s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s4d0g0 : ∀ q (hq : q < x2s4d0.size), 0 ≤ q → q < 1 → ¬ Reach x2s4d0[q].toFinset 4 0 0xeee0eac0 := by
  have check : part x2s4d0 0xeee0eac0 4 0 #[] #[] 0 x2s4d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s4d0ok : correct x2s4d0 4 0 0xeee0eac0 := by
  exact fun q hq => x2s4d0g0 q hq (Nat.zero_le _) hq
def x2s4d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x2s4d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s4d1g0 : ∀ q (hq : q < x2s4d1.size), 0 ≤ q → q < 1 → ¬ Reach x2s4d1[q].toFinset 4 1 0xeee0eac0 := by
  have check : part x2s4d1 0xeee0eac0 4 1 #[] x2s4d0 0 x2s4d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x2s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s4d1ok : correct x2s4d1 4 1 0xeee0eac0 := by
  exact fun q hq => x2s4d1g0 q hq (Nat.zero_le _) hq
def x2s5d0 : Array (List Word) := #[[0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE]]
def x2s5d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s5d0g0 : ∀ q (hq : q < x2s5d0.size), 0 ≤ q → q < 4 → ¬ Reach x2s5d0[q].toFinset 5 0 0xeee0eac0 := by
  have check : part x2s5d0 0xeee0eac0 5 0 x2s4d0 #[] 0 x2s5d0g0c = true := by decide +kernel
  exact part_ok x2s4d0ok (noRows _ _ _) check
def x2s5d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s5d0g4 : ∀ q (hq : q < x2s5d0.size), 4 ≤ q → q < 5 → ¬ Reach x2s5d0[q].toFinset 5 0 0xeee0eac0 := by
  have check : part x2s5d0 0xeee0eac0 5 0 x2s4d0 #[] 4 x2s5d0g4c = true := by decide +kernel
  exact part_ok x2s4d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s5d0ok : correct x2s5d0 5 0 0xeee0eac0 := by
  intro q hq
  have lim : q < 5 := hq
  by_cases atMid : q < 4
  ·
    exact x2s5d0g0 q hq (by omega) (by omega)
  ·
    exact x2s5d0g4 q hq (by omega) (by omega)
def x2s5d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x2s5d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[4,3,2,1,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s5d1g0 : ∀ q (hq : q < x2s5d1.size), 0 ≤ q → q < 1 → ¬ Reach x2s5d1[q].toFinset 5 1 0xeee0eac0 := by
  have check : part x2s5d1 0xeee0eac0 5 1 x2s4d1 x2s5d0 0 x2s5d1g0c = true := by decide +kernel
  exact part_ok x2s4d1ok x2s5d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x2s5d1ok : correct x2s5d1 5 1 0xeee0eac0 := by
  exact fun q hq => x2s5d1g0 q hq (Nat.zero_le _) hq
def x2gates : List Gate := [⟨.or, [3,4]⟩,⟨.and, [0,5]⟩,⟨.or, [1,6]⟩,⟨.or, [4,6]⟩,⟨.and, [3,8]⟩,⟨.or, [2,9]⟩,⟨.and, [7,10]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result2 : Verdict 0xeee0eac0 := by
  apply verdict (k := 5) (by decide) (by decide) (x2s5d1ok 0 (by decide)) x2gates 11
  · simp [x2gates,mono]
  · decide
  · decide +kernel

def x3s2d0 : Array (List Word) := #[[inputA,inputB,0xfff0f000]]
def x3s2d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s2d0g0 : ∀ q (hq : q < x3s2d0.size), 0 ≤ q → q < 1 → ¬ Reach x3s2d0[q].toFinset 2 0 0xeee8e888 := by
  have check : part x3s2d0 0xeee8e888 2 0 #[] #[] 0 x3s2d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s2d0ok : correct x3s2d0 2 0 0xeee8e888 := by
  exact fun q hq => x3s2d0g0 q hq (Nat.zero_le _) hq
def x3s2d1 : Array (List Word) := #[[inputA,inputB,0xfff0f000]]
def x3s2d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s2d1g0 : ∀ q (hq : q < x3s2d1.size), 0 ≤ q → q < 1 → ¬ Reach x3s2d1[q].toFinset 2 1 0xeee8e888 := by
  have check : part x3s2d1 0xeee8e888 2 1 #[] x3s2d0 0 x3s2d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x3s2d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s2d1ok : correct x3s2d1 2 1 0xeee8e888 := by
  exact fun q hq => x3s2d1g0 q hq (Nat.zero_le _) hq
def x3s3d0 : Array (List Word) := #[[inputA,inputB,0xf000f000,0xfff00000],[inputA,inputB,0xf0f00000,0xff00f000],[inputA,inputB,0xf0f0f000,0xff000000],[inputA,inputB,0xfff0f0f0,0xffffff00],[inputA,inputB,0xfff0ff00,0xfffff0f0],[inputA,inputB,0xfff0fff0,0xfffff000]]
def x3s3d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s3d0g0 : ∀ q (hq : q < x3s3d0.size), 0 ≤ q → q < 4 → ¬ Reach x3s3d0[q].toFinset 3 0 0xeee8e888 := by
  have check : part x3s3d0 0xeee8e888 3 0 x3s2d0 #[] 0 x3s3d0g0c = true := by decide +kernel
  exact part_ok x3s2d0ok (noRows _ _ _) check
def x3s3d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s3d0g4 : ∀ q (hq : q < x3s3d0.size), 4 ≤ q → q < 6 → ¬ Reach x3s3d0[q].toFinset 3 0 0xeee8e888 := by
  have check : part x3s3d0 0xeee8e888 3 0 x3s2d0 #[] 4 x3s3d0g4c = true := by decide +kernel
  exact part_ok x3s2d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s3d0ok : correct x3s3d0 3 0 0xeee8e888 := by
  intro q hq
  have lim : q < 6 := hq
  by_cases atMid : q < 4
  ·
    exact x3s3d0g0 q hq (by omega) (by omega)
  ·
    exact x3s3d0g4 q hq (by omega) (by omega)
def x3s3d1 : Array (List Word) := #[[inputA,inputB,0xf000f000,0xfff00000],[inputA,inputB,0xf0f00000,0xff00f000],[inputA,inputB,0xf0f0f000,0xff000000],[inputA,inputB,0xfff0f0f0,0xffffff00],[inputA,inputB,0xfff0ff00,0xfffff0f0],[inputA,inputB,0xfff0fff0,0xfffff000]]
def x3s3d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0]),([0,0,0,0,0,0,0,0,0,0,0,0],[1,1,1,1]),([0,0,0,0,0,0,0,0,0,0,0,0],[2,2,2,2]),([0,0,0,0,0,0,0,0,0,0,0,0],[3,3,3,3])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s3d1g0 : ∀ q (hq : q < x3s3d1.size), 0 ≤ q → q < 4 → ¬ Reach x3s3d1[q].toFinset 3 1 0xeee8e888 := by
  have check : part x3s3d1 0xeee8e888 3 1 x3s2d1 x3s3d0 0 x3s3d1g0c = true := by decide +kernel
  exact part_ok x3s2d1ok x3s3d0ok check
def x3s3d1g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[4,4,4,4]),([0,0,0,0,0,0,0,0,0,0,0,0],[5,5,5,5])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s3d1g4 : ∀ q (hq : q < x3s3d1.size), 4 ≤ q → q < 6 → ¬ Reach x3s3d1[q].toFinset 3 1 0xeee8e888 := by
  have check : part x3s3d1 0xeee8e888 3 1 x3s2d1 x3s3d0 4 x3s3d1g4c = true := by decide +kernel
  exact part_ok x3s2d1ok x3s3d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s3d1ok : correct x3s3d1 3 1 0xeee8e888 := by
  intro q hq
  have lim : q < 6 := hq
  by_cases atMid : q < 4
  ·
    exact x3s3d1g0 q hq (by omega) (by omega)
  ·
    exact x3s3d1g4 q hq (by omega) (by omega)
def x3s4d0 : Array (List Word) := #[[0xf0f0f0,inputA,inputB,inputD,inputE],[0xf00ff00,inputA,inputB,inputC,inputE],[0xfff0000,inputA,inputB,inputC,inputD],[0x70707070,inputA,inputB,inputD,inputE],[0x77007700,inputA,inputB,inputC,inputE],[0x77770000,inputA,inputB,inputC,inputD],[0x88888888,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,inputD,inputE],[inputA,inputB,0xee00ee00,inputC,inputE],[inputA,inputB,0xeeee0000,inputC,inputD],[inputA,inputB,0xf000f000,0xfff0fff0,inputE],[inputA,inputB,0xf0f00000,inputD,0xfffff0f0],[inputA,inputB,0xf0f0f000,inputD,inputE],[inputA,inputB,inputC,0xff000000,0xffffff00],[inputA,inputB,inputC,0xff00f000,inputE],[inputA,inputB,inputC,inputD,0xfff00000],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff000f],[inputA,inputB,inputC,inputD,0xffff1111],[inputA,inputB,inputC,inputD,0xffff8888],[inputA,inputB,inputC,inputD,0xfffff000],[inputA,inputB,inputC,0xff00ff0f,inputE],[inputA,inputB,inputC,0xff11ff11,inputE],[inputA,inputB,inputC,0xff88ff88,inputE],[inputA,inputB,inputC,0xfff0ff00,inputE],[inputA,inputB,0xf0f0f0ff,inputD,inputE],[inputA,inputB,0xf1f1f1f1,inputD,inputE],[inputA,inputB,0xf8f8f8f8,inputD,inputE],[inputA,inputB,inputD,0xfff0f0f0,inputE]]
def x3s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g0 : ∀ q (hq : q < x3s4d0.size), 0 ≤ q → q < 4 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 0 x3s4d0g0c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
def x3s4d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g4 : ∀ q (hq : q < x3s4d0.size), 4 ≤ q → q < 8 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 4 x3s4d0g4c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
def x3s4d0g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,1,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g8 : ∀ q (hq : q < x3s4d0.size), 8 ≤ q → q < 12 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 8 x3s4d0g8c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
def x3s4d0g12c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,2,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g12 : ∀ q (hq : q < x3s4d0.size), 12 ≤ q → q < 16 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 12 x3s4d0g12c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
def x3s4d0g16c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g16 : ∀ q (hq : q < x3s4d0.size), 16 ≤ q → q < 20 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 16 x3s4d0g16c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
def x3s4d0g20c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g20 : ∀ q (hq : q < x3s4d0.size), 20 ≤ q → q < 24 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 20 x3s4d0g20c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
def x3s4d0g24c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g24 : ∀ q (hq : q < x3s4d0.size), 24 ≤ q → q < 28 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 24 x3s4d0g24c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
def x3s4d0g28c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0g28 : ∀ q (hq : q < x3s4d0.size), 28 ≤ q → q < 29 → ¬ Reach x3s4d0[q].toFinset 4 0 0xeee8e888 := by
  have check : part x3s4d0 0xeee8e888 4 0 x3s3d0 #[] 28 x3s4d0g28c = true := by decide +kernel
  exact part_ok x3s3d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d0ok : correct x3s4d0 4 0 0xeee8e888 := by
  intro q hq
  have lim : q < 29 := hq
  by_cases atMid : q < 16
  ·
    by_cases atMid : q < 8
    ·
      by_cases atMid : q < 4
      ·
        exact x3s4d0g0 q hq (by omega) (by omega)
      ·
        exact x3s4d0g4 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 12
      ·
        exact x3s4d0g8 q hq (by omega) (by omega)
      ·
        exact x3s4d0g12 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 24
    ·
      by_cases atMid : q < 20
      ·
        exact x3s4d0g16 q hq (by omega) (by omega)
      ·
        exact x3s4d0g20 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 28
      ·
        exact x3s4d0g24 q hq (by omega) (by omega)
      ·
        exact x3s4d0g28 q hq (by omega) (by omega)
def x3s4d1 : Array (List Word) := #[[0x88888888,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,inputD,inputE],[inputA,inputB,0xee00ee00,inputC,inputE],[inputA,inputB,0xeeee0000,inputC,inputD],[inputA,inputB,0xf000f000,0xfff0fff0,inputE],[inputA,inputB,0xf0f00000,inputD,0xfffff0f0],[inputA,inputB,0xf0f0f000,inputD,inputE],[inputA,inputB,inputC,0xff000000,0xffffff00],[inputA,inputB,inputC,0xff00f000,inputE],[inputA,inputB,inputC,inputD,0xfff00000],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff8888],[inputA,inputB,inputC,inputD,0xfffff000],[inputA,inputB,inputC,0xff88ff88,inputE],[inputA,inputB,inputC,0xfff0ff00,inputE],[inputA,inputB,0xf8f8f8f8,inputD,inputE],[inputA,inputB,inputD,0xfff0f0f0,inputE]]
def x3s4d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[6,6,6,6,6]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[7,7,7,7,7]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[8,8,8,8,8]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[9,9,9,9,9])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d1g0 : ∀ q (hq : q < x3s4d1.size), 0 ≤ q → q < 4 → ¬ Reach x3s4d1[q].toFinset 4 1 0xeee8e888 := by
  have check : part x3s4d1 0xeee8e888 4 1 x3s3d1 x3s4d0 0 x3s4d1g0c = true := by decide +kernel
  exact part_ok x3s3d1ok x3s4d0ok check
def x3s4d1g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0],[10,10,10,10,10]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,1,0],[11,11,11,11,11]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0],[12,12,12,12,12]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,2,0],[13,13,13,13,13])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d1g4 : ∀ q (hq : q < x3s4d1.size), 4 ≤ q → q < 8 → ¬ Reach x3s4d1[q].toFinset 4 1 0xeee8e888 := by
  have check : part x3s4d1 0xeee8e888 4 1 x3s3d1 x3s4d0 4 x3s4d1g4c = true := by decide +kernel
  exact part_ok x3s3d1ok x3s4d0ok check
def x3s4d1g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],[14,14,14,14,14]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[15,15,15,15,15]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[16,16,16,16,16]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[19,19,19,19,19])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d1g8 : ∀ q (hq : q < x3s4d1.size), 8 ≤ q → q < 12 → ¬ Reach x3s4d1[q].toFinset 4 1 0xeee8e888 := by
  have check : part x3s4d1 0xeee8e888 4 1 x3s3d1 x3s4d0 8 x3s4d1g8c = true := by decide +kernel
  exact part_ok x3s3d1ok x3s4d0ok check
def x3s4d1g12c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0],[20,20,20,20,20]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[23,23,23,23,23]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0],[24,24,24,24,24]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[27,27,27,27,27])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d1g12 : ∀ q (hq : q < x3s4d1.size), 12 ≤ q → q < 16 → ¬ Reach x3s4d1[q].toFinset 4 1 0xeee8e888 := by
  have check : part x3s4d1 0xeee8e888 4 1 x3s3d1 x3s4d0 12 x3s4d1g12c = true := by decide +kernel
  exact part_ok x3s3d1ok x3s4d0ok check
def x3s4d1g16c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0],[28,28,28,28,28])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d1g16 : ∀ q (hq : q < x3s4d1.size), 16 ≤ q → q < 17 → ¬ Reach x3s4d1[q].toFinset 4 1 0xeee8e888 := by
  have check : part x3s4d1 0xeee8e888 4 1 x3s3d1 x3s4d0 16 x3s4d1g16c = true := by decide +kernel
  exact part_ok x3s3d1ok x3s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s4d1ok : correct x3s4d1 4 1 0xeee8e888 := by
  intro q hq
  have lim : q < 17 := hq
  by_cases atMid : q < 8
  ·
    by_cases atMid : q < 4
    ·
      exact x3s4d1g0 q hq (by omega) (by omega)
    ·
      exact x3s4d1g4 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 12
    ·
      exact x3s4d1g8 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 16
      ·
        exact x3s4d1g12 q hq (by omega) (by omega)
      ·
        exact x3s4d1g16 q hq (by omega) (by omega)
def x3s5d0 : Array (List Word) := #[[0xff,inputA,inputB,inputC,inputD,inputE],[0xf0f,inputA,inputB,inputC,inputD,inputE],[0x3333,inputA,inputB,inputC,inputD,inputE],[0x5555,inputA,inputB,inputC,inputD,inputE],[0xaaaa,inputA,inputB,inputC,inputD,inputE],[0xcccc,inputA,inputB,inputC,inputD,inputE],[0xf0f0,inputA,inputB,inputC,inputD,inputE],[0xff00,inputA,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,inputE],[0xf000f,inputA,inputB,inputC,inputD,inputE],[0x330033,inputA,inputB,inputC,inputD,inputE],[0x550055,inputA,inputB,inputC,inputD,inputE],[0xaa00aa,inputA,inputB,inputC,inputD,inputE],[0xcc00cc,inputA,inputB,inputC,inputD,inputE],[0xf000f0,inputA,inputB,inputC,inputD,inputE],[0xff0000,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xffffff,inputA,inputB,inputC,inputD,inputE],[0x3030303,inputA,inputB,inputC,inputD,inputE],[0x5050505,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a,inputA,inputB,inputC,inputD,inputE],[0xc0c0c0c,inputA,inputB,inputC,inputD,inputE],[0xf000f00,inputA,inputB,inputC,inputD,inputE],[0xf0f0000,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0xf0fffff,inputA,inputB,inputC,inputD,inputE],[0xfff0fff,inputA,inputB,inputC,inputD,inputE],[0x11111111,inputA,inputB,inputC,inputD,inputE],[0x22222222,inputA,inputB,inputC,inputD,inputE],[0x30303030,inputA,inputB,inputC,inputD,inputE],[0x33003300,inputA,inputB,inputC,inputD,inputE],[0x33330000,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x3333ffff,inputA,inputB,inputC,inputD,inputE],[0x33ff33ff,inputA,inputB,inputC,inputD,inputE],[0x3f3f3f3f,inputA,inputB,inputC,inputD,inputE],[0x44444444,inputA,inputB,inputC,inputD,inputE],[0x50505050,inputA,inputB,inputC,inputD,inputE],[0x55005500,inputA,inputB,inputC,inputD,inputE],[0x55550000,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE],[0x5555ffff,inputA,inputB,inputC,inputD,inputE],[0x55ff55ff,inputA,inputB,inputC,inputD,inputE],[0x5f5f5f5f,inputA,inputB,inputC,inputD,inputE],[0x77777777,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[inputA,0xaaffaaff,inputB,inputC,inputD,inputE],[inputA,0xafafafaf,inputB,inputC,inputD,inputE],[inputA,0xbbbbbbbb,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,inputB,0xccccffff,inputC,inputD,inputE],[inputA,inputB,0xccffccff,inputC,inputD,inputE],[inputA,inputB,0xcfcfcfcf,inputC,inputD,inputE],[inputA,inputB,0xdddddddd,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[inputA,inputB,inputC,0xf0fff0ff,inputD,inputE],[inputA,inputB,inputC,0xf3f3f3f3,inputD,inputE],[inputA,inputB,inputC,0xf5f5f5f5,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,inputC,0xff000000,inputD,inputE],[inputA,inputB,inputC,inputD,0xff00ffff,inputE],[inputA,inputB,inputC,inputD,0xff0fff0f,inputE],[inputA,inputB,inputC,inputD,0xff33ff33,inputE],[inputA,inputB,inputC,inputD,0xff55ff55,inputE],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,inputD,inputE,0xffff00ff],[inputA,inputB,inputC,inputD,inputE,0xffff0f0f],[inputA,inputB,inputC,inputD,inputE,0xffff3333],[inputA,inputB,inputC,inputD,inputE,0xffff5555],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xffffff00]]
def x3s5d0g0c : List (List ℕ × List ℕ) := [([16,16,16,16,16,0xc810,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,0xa810,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g0 : ∀ q (hq : q < x3s5d0.size), 0 ≤ q → q < 4 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 0 x3s5d0g0c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g4c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g4 : ∀ q (hq : q < x3s5d0.size), 4 ≤ q → q < 8 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 4 x3s5d0g4c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g8c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,0x8810,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g8 : ∀ q (hq : q < x3s5d0.size), 8 ≤ q → q < 12 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 8 x3s5d0g8c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g12c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g12 : ∀ q (hq : q < x3s5d0.size), 12 ≤ q → q < 16 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 12 x3s5d0g12c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g16c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g16 : ∀ q (hq : q < x3s5d0.size), 16 ≤ q → q < 20 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 16 x3s5d0g16c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g20c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g20 : ∀ q (hq : q < x3s5d0.size), 20 ≤ q → q < 24 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 20 x3s5d0g20c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g24c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,0x810,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,0x1010,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,0xd010,16,0xb010,16,0x9010,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g24 : ∀ q (hq : q < x3s5d0.size), 24 ≤ q → q < 28 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 24 x3s5d0g24c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g28c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g28 : ∀ q (hq : q < x3s5d0.size), 28 ≤ q → q < 32 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 28 x3s5d0g28c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g32c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g32 : ∀ q (hq : q < x3s5d0.size), 32 ≤ q → q < 36 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 32 x3s5d0g32c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g36c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g36 : ∀ q (hq : q < x3s5d0.size), 36 ≤ q → q < 40 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 36 x3s5d0g36c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g40c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g40 : ∀ q (hq : q < x3s5d0.size), 40 ≤ q → q < 44 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 40 x3s5d0g40c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g44c : List (List ℕ × List ℕ) := [([16,16,0x1810,16,0x2010,16,0x2810,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,0xd810,16,0xb810,16,0x9810,0x3010,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g44 : ∀ q (hq : q < x3s5d0.size), 44 ≤ q → q < 48 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 44 x3s5d0g44c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g48c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g48 : ∀ q (hq : q < x3s5d0.size), 48 ≤ q → q < 52 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 48 x3s5d0g48c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g52c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g52 : ∀ q (hq : q < x3s5d0.size), 52 ≤ q → q < 56 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 52 x3s5d0g52c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g56c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g56 : ∀ q (hq : q < x3s5d0.size), 56 ≤ q → q < 60 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 56 x3s5d0g56c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g60c : List (List ℕ × List ℕ) := [([0x3010,16,16,16,16,16,16,16,16,16,16,16,16,0x3810,16,0x4010,16,0x4810,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,0xa010,0x5010,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,0xc010,16,16,0x5810,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g60 : ∀ q (hq : q < x3s5d0.size), 60 ≤ q → q < 64 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 60 x3s5d0g60c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g64c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g64 : ∀ q (hq : q < x3s5d0.size), 64 ≤ q → q < 68 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 64 x3s5d0g64c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g68c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,0xe010,16,16,16,16,0x6810],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g68 : ∀ q (hq : q < x3s5d0.size), 68 ≤ q → q < 72 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 68 x3s5d0g68c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g72c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g72 : ∀ q (hq : q < x3s5d0.size), 72 ≤ q → q < 76 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 72 x3s5d0g72c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g76c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,0x5010,16,16,16,16,0x7810,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g76 : ∀ q (hq : q < x3s5d0.size), 76 ≤ q → q < 80 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 76 x3s5d0g76c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g80c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16],[]),([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,0x5810,16,16,0x7010,16],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g80 : ∀ q (hq : q < x3s5d0.size), 80 ≤ q → q < 84 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 80 x3s5d0g80c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
def x3s5d0g84c : List (List ℕ × List ℕ) := [([16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,0x6010,16,0x6810],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0g84 : ∀ q (hq : q < x3s5d0.size), 84 ≤ q → q < 85 → ¬ Reach x3s5d0[q].toFinset 5 0 0xeee8e888 := by
  have check : part x3s5d0 0xeee8e888 5 0 x3s4d0 #[] 84 x3s5d0g84c = true := by decide +kernel
  exact part_ok x3s4d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d0ok : correct x3s5d0 5 0 0xeee8e888 := by
  intro q hq
  have lim : q < 85 := hq
  by_cases atMid : q < 44
  ·
    by_cases atMid : q < 20
    ·
      by_cases atMid : q < 8
      ·
        by_cases atMid : q < 4
        ·
          exact x3s5d0g0 q hq (by omega) (by omega)
        ·
          exact x3s5d0g4 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 12
        ·
          exact x3s5d0g8 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 16
          ·
            exact x3s5d0g12 q hq (by omega) (by omega)
          ·
            exact x3s5d0g16 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 32
      ·
        by_cases atMid : q < 24
        ·
          exact x3s5d0g20 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 28
          ·
            exact x3s5d0g24 q hq (by omega) (by omega)
          ·
            exact x3s5d0g28 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 36
        ·
          exact x3s5d0g32 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 40
          ·
            exact x3s5d0g36 q hq (by omega) (by omega)
          ·
            exact x3s5d0g40 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 64
    ·
      by_cases atMid : q < 52
      ·
        by_cases atMid : q < 48
        ·
          exact x3s5d0g44 q hq (by omega) (by omega)
        ·
          exact x3s5d0g48 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 56
        ·
          exact x3s5d0g52 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 60
          ·
            exact x3s5d0g56 q hq (by omega) (by omega)
          ·
            exact x3s5d0g60 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 76
      ·
        by_cases atMid : q < 68
        ·
          exact x3s5d0g64 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 72
          ·
            exact x3s5d0g68 q hq (by omega) (by omega)
          ·
            exact x3s5d0g72 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 80
        ·
          exact x3s5d0g76 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 84
          ·
            exact x3s5d0g80 q hq (by omega) (by omega)
          ·
            exact x3s5d0g84 q hq (by omega) (by omega)
def x3s5d1 : Array (List Word) := #[[0x88888888,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,inputC,0xff000000,inputD,inputE],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xffffff00]]
def x3s5d1g0c : List (List ℕ × List ℕ) := [([10,0x780a,10,0x680a,10,0x580a,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x1602d,0x1402d,0x1002d,0xc02d,0x802d,0x402d]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x1582e,0x1402e,0x1002e,0xc02e,0x802e,0x402e]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x1502f,0x1402f,0x1002f,0xc02f,0x802f,0x402f]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14830,0x14030,0x10030,0xc030,0x8030,0x4030])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d1g0 : ∀ q (hq : q < x3s5d1.size), 0 ≤ q → q < 4 → ¬ Reach x3s5d1[q].toFinset 5 1 0xeee8e888 := by
  have check : part x3s5d1 0xeee8e888 5 1 x3s4d1 x3s5d0 0 x3s5d1g0c = true := by decide +kernel
  exact part_ok x3s4d1ok x3s5d0ok check
def x3s5d1g4c : List (List ℕ × List ℕ) := [([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14035,0x11835,0x10035,0xc035,0x8035,0x4035]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14036,0x11036,0x10036,0xc036,0x8036,0x4036]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14037,0x10837,0x10037,0xc037,0x8037,0x4037]),([10,10,10,10,10,10,10,10,10,10,10,10,10,0x80a,10,0x100a,10,0x180a,10,10,10,10,10,10,10],[0x1403c,0x1003c,0xd83c,0xc03c,0x803c,0x403c])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d1g4 : ∀ q (hq : q < x3s5d1.size), 4 ≤ q → q < 8 → ¬ Reach x3s5d1[q].toFinset 5 1 0xeee8e888 := by
  have check : part x3s5d1 0xeee8e888 5 1 x3s4d1 x3s5d0 4 x3s5d1g4c = true := by decide +kernel
  exact part_ok x3s4d1ok x3s5d0ok check
def x3s5d1g8c : List (List ℕ × List ℕ) := [([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,0x600a,0x200a,10,10,10,10],[0x1403d,0x1003d,0xd03d,0xc03d,0x803d,0x403d]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,0x700a,10,10,0x280a,10,10],[0x1403e,0x1003e,0xc83e,0xc03e,0x803e,0x403e]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14043,0x10043,0xc043,0x9843,0x8043,0x4043]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14044,0x10044,0xc044,0x9044,0x8044,0x4044])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d1g8 : ∀ q (hq : q < x3s5d1.size), 8 ≤ q → q < 12 → ¬ Reach x3s5d1[q].toFinset 5 1 0xeee8e888 := by
  have check : part x3s5d1 0xeee8e888 5 1 x3s4d1 x3s5d0 8 x3s5d1g8c = true := by decide +kernel
  exact part_ok x3s4d1ok x3s5d0ok check
def x3s5d1g12c : List (List ℕ × List ℕ) := [([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,0x800a,10,10,10,10,0x380a],[0x14045,0x10045,0xc045,0x8845,0x8045,0x4045]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x1404a,0x1004a,0xc04a,0x804a,0x584a,0x404a]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x1404b,0x1004b,0xc04b,0x804b,0x504b,0x404b]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,0x200a,10,10,10,10,0x480a,10],[0x1404c,0x1004c,0xc04c,0x804c,0x484c,0x404c])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d1g12 : ∀ q (hq : q < x3s5d1.size), 12 ≤ q → q < 16 → ¬ Reach x3s5d1[q].toFinset 5 1 0xeee8e888 := by
  have check : part x3s5d1 0xeee8e888 5 1 x3s4d1 x3s5d0 12 x3s5d1g12c = true := by decide +kernel
  exact part_ok x3s4d1ok x3s5d0ok check
def x3s5d1g16c : List (List ℕ × List ℕ) := [([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14051,0x10051,0xc051,0x8051,0x4051,0x1851]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10],[0x14052,0x10052,0xc052,0x8052,0x4052,0x1052]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,0x280a,10,10,0x400a,10],[0x14053,0x10053,0xc053,0x8053,0x4053,0x853]),([10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,0x300a,10,0x380a],[0x14054,0x10054,0xc054,0x8054,0x4054,0x54])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d1g16 : ∀ q (hq : q < x3s5d1.size), 16 ≤ q → q < 20 → ¬ Reach x3s5d1[q].toFinset 5 1 0xeee8e888 := by
  have check : part x3s5d1 0xeee8e888 5 1 x3s4d1 x3s5d0 16 x3s5d1g16c = true := by decide +kernel
  exact part_ok x3s4d1ok x3s5d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s5d1ok : correct x3s5d1 5 1 0xeee8e888 := by
  intro q hq
  have lim : q < 20 := hq
  by_cases atMid : q < 8
  ·
    by_cases atMid : q < 4
    ·
      exact x3s5d1g0 q hq (by omega) (by omega)
    ·
      exact x3s5d1g4 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 12
    ·
      exact x3s5d1g8 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 16
      ·
        exact x3s5d1g12 q hq (by omega) (by omega)
      ·
        exact x3s5d1g16 q hq (by omega) (by omega)
def x3s6d0 : Array (List Word) := #[[0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE]]
def x3s6d0g0c : List (List ℕ × List ℕ) := [([0x2008,0x18808,0x2808,0x1c008,0x3008,0x1f808,0x3808,0x23008,0x16808,0x1e008,0x17008,0x21808,0x17808,0x25008,0x18008,0x28808,0x1a808,0x22008,0x1b008,0x25808,0x1b808,0x29008,0x1e808,0x26008,0x1f008,0x29808,0x22808,0x2a008],[]),([0x6010,0x19010,0x6810,0x1c810,0x7010,0x20010,0x7810,0x26810,0x16810,0x1e010,0x17010,0x21810,0x17810,0x25010,0x18010,0x28810,0x1a810,0x22010,0x1b010,0x25810,0x1b810,0x29010,0x1e810,0x26010,0x1f010,0x29810,0x22810,0x2a010],[]),([0xa018,0x19818,0xa818,0x1d018,0xb018,0x23818,0xb818,0x27018,0x16818,0x1e018,0x17018,0x21818,0x17818,0x25018,0x18018,0x28818,0x1a818,0x22018,0x1b018,0x25818,0x1b818,0x29018,0x1e818,0x26018,0x1f018,0x29818,0x22818,0x2a018],[]),([0xe020,0x1a020,0xe820,0x20820,0xf020,0x24020,0xf820,0x27820,0x16820,0x1e020,0x17020,0x21820,0x17820,0x25020,0x18020,0x28820,0x1a820,0x22020,0x1b020,0x25820,0x1b820,0x29020,0x1e820,0x26020,0x1f020,0x29820,0x22820,0x2a020],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s6d0g0 : ∀ q (hq : q < x3s6d0.size), 0 ≤ q → q < 4 → ¬ Reach x3s6d0[q].toFinset 6 0 0xeee8e888 := by
  have check : part x3s6d0 0xeee8e888 6 0 x3s5d0 #[] 0 x3s6d0g0c = true := by decide +kernel
  exact part_ok x3s5d0ok (noRows _ _ _) check
def x3s6d0g4c : List (List ℕ × List ℕ) := [([0x12028,0x1d828,0x12828,0x21028,0x13028,0x24828,0x13828,0x28028,0x16828,0x1e028,0x17028,0x21828,0x17828,0x25028,0x18028,0x28828,0x1a828,0x22028,0x1b028,0x25828,0x1b828,0x29028,0x1e828,0x26028,0x1f028,0x29828,0x22828,0x2a028],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s6d0g4 : ∀ q (hq : q < x3s6d0.size), 4 ≤ q → q < 5 → ¬ Reach x3s6d0[q].toFinset 6 0 0xeee8e888 := by
  have check : part x3s6d0 0xeee8e888 6 0 x3s5d0 #[] 4 x3s6d0g4c = true := by decide +kernel
  exact part_ok x3s5d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s6d0ok : correct x3s6d0 6 0 0xeee8e888 := by
  intro q hq
  have lim : q < 5 := hq
  by_cases atMid : q < 4
  ·
    exact x3s6d0g0 q hq (by omega) (by omega)
  ·
    exact x3s6d0g4 q hq (by omega) (by omega)
def x3s6d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x3s6d1g0c : List (List ℕ × List ℕ) := [([0,7,1,10,2,13,3,16,4,11,5,14,6,17,8,15,9,18,12,19],[4,3,2,1,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s6d1g0 : ∀ q (hq : q < x3s6d1.size), 0 ≤ q → q < 1 → ¬ Reach x3s6d1[q].toFinset 6 1 0xeee8e888 := by
  have check : part x3s6d1 0xeee8e888 6 1 x3s5d1 x3s6d0 0 x3s6d1g0c = true := by decide +kernel
  exact part_ok x3s5d1ok x3s6d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x3s6d1ok : correct x3s6d1 6 1 0xeee8e888 := by
  exact fun q hq => x3s6d1g0 q hq (Nat.zero_le _) hq
def x3gates : List Gate := [⟨.and, [0,1]⟩,⟨.or, [0,1]⟩,⟨.or, [2,3]⟩,⟨.and, [2,3]⟩,⟨.or, [4,8]⟩,⟨.and, [7,9]⟩,⟨.and, [6,10]⟩,⟨.or, [5,11]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result3 : Verdict 0xeee8e888 := by
  apply verdict (k := 6) (by decide) (by decide) (x3s6d1ok 0 (by decide)) x3gates 12
  · simp [x3gates,mono]
  · decide
  · decide +kernel

def x4s2d0 : Array (List Word) := #[[inputA,0xcccccc00,0xfff0f0f0]]
def x4s2d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s2d0g0 : ∀ q (hq : q < x4s2d0.size), 0 ≤ q → q < 1 → ¬ Reach x4s2d0[q].toFinset 2 0 0xeee8e8a0 := by
  have check : part x4s2d0 0xeee8e8a0 2 0 #[] #[] 0 x4s2d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s2d0ok : correct x4s2d0 2 0 0xeee8e8a0 := by
  exact fun q hq => x4s2d0g0 q hq (Nat.zero_le _) hq
def x4s2d1 : Array (List Word) := #[[inputA,0xcccccc00,0xfff0f0f0]]
def x4s2d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s2d1g0 : ∀ q (hq : q < x4s2d1.size), 0 ≤ q → q < 1 → ¬ Reach x4s2d1[q].toFinset 2 1 0xeee8e8a0 := by
  have check : part x4s2d1 0xeee8e8a0 2 1 #[] x4s2d0 0 x4s2d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x4s2d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s2d1ok : correct x4s2d1 2 1 0xeee8e8a0 := by
  exact fun q hq => x4s2d1g0 q hq (Nat.zero_le _) hq
def x4s3d0 : Array (List Word) := #[[inputA,0xcccccc00,inputC,0xff000000],[inputA,inputB,0xfff0f0f0,0xffffff00]]
def x4s3d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s3d0g0 : ∀ q (hq : q < x4s3d0.size), 0 ≤ q → q < 2 → ¬ Reach x4s3d0[q].toFinset 3 0 0xeee8e8a0 := by
  have check : part x4s3d0 0xeee8e8a0 3 0 x4s2d0 #[] 0 x4s3d0g0c = true := by decide +kernel
  exact part_ok x4s2d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s3d0ok : correct x4s3d0 3 0 0xeee8e8a0 := by
  exact fun q hq => x4s3d0g0 q hq (Nat.zero_le _) hq
def x4s3d1 : Array (List Word) := #[[inputA,0xcccccc00,inputC,0xff000000],[inputA,inputB,0xfff0f0f0,0xffffff00]]
def x4s3d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0]),([0,0,0,0,0,0,0,0,0,0,0,0],[1,1,1,1])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s3d1g0 : ∀ q (hq : q < x4s3d1.size), 0 ≤ q → q < 2 → ¬ Reach x4s3d1[q].toFinset 3 1 0xeee8e8a0 := by
  have check : part x4s3d1 0xeee8e8a0 3 1 x4s2d1 x4s3d0 0 x4s3d1g0c = true := by decide +kernel
  exact part_ok x4s2d1ok x4s3d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s3d1ok : correct x4s3d1 3 1 0xeee8e8a0 := by
  exact fun q hq => x4s3d1g0 q hq (Nat.zero_le _) hq
def x4s4d0 : Array (List Word) := #[[0xf0f0f0,inputA,inputB,inputD,inputE],[0xf00ff00,inputA,inputB,inputC,inputE],[0xfff0000,inputA,inputB,inputC,inputD],[0x4c4c4c4c,inputA,inputC,inputD,inputE],[0x5f005f00,inputA,inputB,inputC,inputE],[0x5f5f0000,inputA,inputB,inputC,inputD],[inputA,0xcccccc00,inputC,inputD,inputE],[inputA,inputB,0xcf00cf00,inputC,inputE],[inputA,inputB,0xcfcf0000,inputC,inputD],[inputA,inputB,0xe0e0e0e0,inputD,inputE],[inputA,inputB,0xee00ee00,inputC,inputE],[inputA,inputB,0xeeee0000,inputC,inputD],[inputA,inputB,inputC,0xff000000,0xffffff00],[inputA,inputB,inputC,0xff00cc00,inputE],[inputA,inputB,inputC,inputD,0xffcc0000],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff0033],[inputA,inputB,inputC,inputD,0xffff1111],[inputA,inputB,inputC,inputD,0xffff3030],[inputA,inputB,inputC,inputD,0xffffa0a0],[inputA,inputB,inputC,inputD,0xfffff000],[inputA,inputB,inputC,0xff00ff33,inputE],[inputA,inputB,inputC,0xff11ff11,inputE],[inputA,inputB,inputC,0xff30ff30,inputE],[inputA,inputB,inputC,0xffa0ffa0,inputE],[inputA,inputB,inputC,0xfff0ff00,inputE],[inputA,inputB,0xf1f1f1f1,inputD,inputE],[inputA,inputB,inputD,0xfff0f0f0,inputE],[inputA,0xccccccff,inputC,inputD,inputE],[inputA,0xecececec,inputC,inputD,inputE]]
def x4s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g0 : ∀ q (hq : q < x4s4d0.size), 0 ≤ q → q < 4 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 0 x4s4d0g0c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
def x4s4d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g4 : ∀ q (hq : q < x4s4d0.size), 4 ≤ q → q < 8 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 4 x4s4d0g4c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
def x4s4d0g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g8 : ∀ q (hq : q < x4s4d0.size), 8 ≤ q → q < 12 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 8 x4s4d0g8c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
def x4s4d0g12c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g12 : ∀ q (hq : q < x4s4d0.size), 12 ≤ q → q < 16 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 12 x4s4d0g12c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
def x4s4d0g16c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g16 : ∀ q (hq : q < x4s4d0.size), 16 ≤ q → q < 20 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 16 x4s4d0g16c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
def x4s4d0g20c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g20 : ∀ q (hq : q < x4s4d0.size), 20 ≤ q → q < 24 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 20 x4s4d0g20c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
def x4s4d0g24c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g24 : ∀ q (hq : q < x4s4d0.size), 24 ≤ q → q < 28 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 24 x4s4d0g24c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
def x4s4d0g28c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0g28 : ∀ q (hq : q < x4s4d0.size), 28 ≤ q → q < 30 → ¬ Reach x4s4d0[q].toFinset 4 0 0xeee8e8a0 := by
  have check : part x4s4d0 0xeee8e8a0 4 0 x4s3d0 #[] 28 x4s4d0g28c = true := by decide +kernel
  exact part_ok x4s3d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d0ok : correct x4s4d0 4 0 0xeee8e8a0 := by
  intro q hq
  have lim : q < 30 := hq
  by_cases atMid : q < 16
  ·
    by_cases atMid : q < 8
    ·
      by_cases atMid : q < 4
      ·
        exact x4s4d0g0 q hq (by omega) (by omega)
      ·
        exact x4s4d0g4 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 12
      ·
        exact x4s4d0g8 q hq (by omega) (by omega)
      ·
        exact x4s4d0g12 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 24
    ·
      by_cases atMid : q < 20
      ·
        exact x4s4d0g16 q hq (by omega) (by omega)
      ·
        exact x4s4d0g20 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 28
      ·
        exact x4s4d0g24 q hq (by omega) (by omega)
      ·
        exact x4s4d0g28 q hq (by omega) (by omega)
def x4s4d1 : Array (List Word) := #[[inputA,0xcccccc00,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,inputD,inputE],[inputA,inputB,0xee00ee00,inputC,inputE],[inputA,inputB,0xeeee0000,inputC,inputD],[inputA,inputB,inputC,0xff000000,0xffffff00],[inputA,inputB,inputC,0xff00cc00,inputE],[inputA,inputB,inputC,inputD,0xffcc0000],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffffa0a0],[inputA,inputB,inputC,inputD,0xfffff000],[inputA,inputB,inputC,0xffa0ffa0,inputE],[inputA,inputB,inputC,0xfff0ff00,inputE],[inputA,inputB,inputD,0xfff0f0f0,inputE],[inputA,0xecececec,inputC,inputD,inputE]]
def x4s4d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[6,6,6,6,6]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[9,9,9,9,9]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[10,10,10,10,10]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[11,11,11,11,11])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d1g0 : ∀ q (hq : q < x4s4d1.size), 0 ≤ q → q < 4 → ¬ Reach x4s4d1[q].toFinset 4 1 0xeee8e8a0 := by
  have check : part x4s4d1 0xeee8e8a0 4 1 x4s3d1 x4s4d0 0 x4s4d1g0c = true := by decide +kernel
  exact part_ok x4s3d1ok x4s4d0ok check
def x4s4d1g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],[12,12,12,12,12]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[13,13,13,13,13]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[14,14,14,14,14]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[15,15,15,15,15])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d1g4 : ∀ q (hq : q < x4s4d1.size), 4 ≤ q → q < 8 → ¬ Reach x4s4d1[q].toFinset 4 1 0xeee8e8a0 := by
  have check : part x4s4d1 0xeee8e8a0 4 1 x4s3d1 x4s4d0 4 x4s4d1g4c = true := by decide +kernel
  exact part_ok x4s3d1ok x4s4d0ok check
def x4s4d1g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[19,19,19,19,19]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[20,20,20,20,20]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[24,24,24,24,24]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[25,25,25,25,25])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d1g8 : ∀ q (hq : q < x4s4d1.size), 8 ≤ q → q < 12 → ¬ Reach x4s4d1[q].toFinset 4 1 0xeee8e8a0 := by
  have check : part x4s4d1 0xeee8e8a0 4 1 x4s3d1 x4s4d0 8 x4s4d1g8c = true := by decide +kernel
  exact part_ok x4s3d1ok x4s4d0ok check
def x4s4d1g12c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],[27,27,27,27,27]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[29,29,29,29,29])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d1g12 : ∀ q (hq : q < x4s4d1.size), 12 ≤ q → q < 14 → ¬ Reach x4s4d1[q].toFinset 4 1 0xeee8e8a0 := by
  have check : part x4s4d1 0xeee8e8a0 4 1 x4s3d1 x4s4d0 12 x4s4d1g12c = true := by decide +kernel
  exact part_ok x4s3d1ok x4s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s4d1ok : correct x4s4d1 4 1 0xeee8e8a0 := by
  intro q hq
  have lim : q < 14 := hq
  by_cases atMid : q < 8
  ·
    by_cases atMid : q < 4
    ·
      exact x4s4d1g0 q hq (by omega) (by omega)
    ·
      exact x4s4d1g4 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 12
    ·
      exact x4s4d1g8 q hq (by omega) (by omega)
    ·
      exact x4s4d1g12 q hq (by omega) (by omega)
def x4s5d0 : Array (List Word) := #[[0xff,inputA,inputB,inputC,inputD,inputE],[0xf0f,inputA,inputB,inputC,inputD,inputE],[0x3333,inputA,inputB,inputC,inputD,inputE],[0x5555,inputA,inputB,inputC,inputD,inputE],[0xaaaa,inputA,inputB,inputC,inputD,inputE],[0xcccc,inputA,inputB,inputC,inputD,inputE],[0xf0f0,inputA,inputB,inputC,inputD,inputE],[0xff00,inputA,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,inputE],[0xf000f,inputA,inputB,inputC,inputD,inputE],[0x330033,inputA,inputB,inputC,inputD,inputE],[0x550055,inputA,inputB,inputC,inputD,inputE],[0xaa00aa,inputA,inputB,inputC,inputD,inputE],[0xcc00cc,inputA,inputB,inputC,inputD,inputE],[0xf000f0,inputA,inputB,inputC,inputD,inputE],[0xff0000,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xffffff,inputA,inputB,inputC,inputD,inputE],[0x3030303,inputA,inputB,inputC,inputD,inputE],[0x5050505,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a,inputA,inputB,inputC,inputD,inputE],[0xc0c0c0c,inputA,inputB,inputC,inputD,inputE],[0xf000f00,inputA,inputB,inputC,inputD,inputE],[0xf0f0000,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0xf0fffff,inputA,inputB,inputC,inputD,inputE],[0xfff0fff,inputA,inputB,inputC,inputD,inputE],[0x11111111,inputA,inputB,inputC,inputD,inputE],[0x22222222,inputA,inputB,inputC,inputD,inputE],[0x30303030,inputA,inputB,inputC,inputD,inputE],[0x33003300,inputA,inputB,inputC,inputD,inputE],[0x33330000,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x3333ffff,inputA,inputB,inputC,inputD,inputE],[0x33ff33ff,inputA,inputB,inputC,inputD,inputE],[0x3f3f3f3f,inputA,inputB,inputC,inputD,inputE],[0x44444444,inputA,inputB,inputC,inputD,inputE],[0x50505050,inputA,inputB,inputC,inputD,inputE],[0x55005500,inputA,inputB,inputC,inputD,inputE],[0x55550000,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE],[0x5555ffff,inputA,inputB,inputC,inputD,inputE],[0x55ff55ff,inputA,inputB,inputC,inputD,inputE],[0x5f5f5f5f,inputA,inputB,inputC,inputD,inputE],[0x77777777,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[inputA,0xaaffaaff,inputB,inputC,inputD,inputE],[inputA,0xafafafaf,inputB,inputC,inputD,inputE],[inputA,0xbbbbbbbb,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,inputB,0xccccffff,inputC,inputD,inputE],[inputA,inputB,0xccffccff,inputC,inputD,inputE],[inputA,inputB,0xcfcfcfcf,inputC,inputD,inputE],[inputA,inputB,0xdddddddd,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[inputA,inputB,inputC,0xf0fff0ff,inputD,inputE],[inputA,inputB,inputC,0xf3f3f3f3,inputD,inputE],[inputA,inputB,inputC,0xf5f5f5f5,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,inputC,0xff000000,inputD,inputE],[inputA,inputB,inputC,inputD,0xff00ffff,inputE],[inputA,inputB,inputC,inputD,0xff0fff0f,inputE],[inputA,inputB,inputC,inputD,0xff33ff33,inputE],[inputA,inputB,inputC,inputD,0xff55ff55,inputE],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,inputD,inputE,0xffff00ff],[inputA,inputB,inputC,inputD,inputE,0xffff0f0f],[inputA,inputB,inputC,inputD,inputE,0xffff3333],[inputA,inputB,inputC,inputD,inputE,0xffff5555],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xffffff00]]
def x4s5d0g0c : List (List ℕ × List ℕ) := [([15,15,15,0xe00f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,0xa80f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g0 : ∀ q (hq : q < x4s5d0.size), 0 ≤ q → q < 4 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 0 x4s5d0g0c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g4c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g4 : ∀ q (hq : q < x4s5d0.size), 4 ≤ q → q < 8 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 4 x4s5d0g4c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g8c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,0x800f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g8 : ∀ q (hq : q < x4s5d0.size), 8 ≤ q → q < 12 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 8 x4s5d0g8c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g12c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g12 : ∀ q (hq : q < x4s5d0.size), 12 ≤ q → q < 16 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 12 x4s5d0g12c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g16c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g16 : ∀ q (hq : q < x4s5d0.size), 16 ≤ q → q < 20 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 16 x4s5d0g16c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g20c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g20 : ∀ q (hq : q < x4s5d0.size), 20 ≤ q → q < 24 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 20 x4s5d0g20c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g24c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,0x80f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,0x100f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,0xd00f,15,0xb00f,15,0x880f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g24 : ∀ q (hq : q < x4s5d0.size), 24 ≤ q → q < 28 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 24 x4s5d0g24c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g28c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,0xb80f,15,0x900f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g28 : ∀ q (hq : q < x4s5d0.size), 28 ≤ q → q < 32 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 28 x4s5d0g28c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g32c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g32 : ∀ q (hq : q < x4s5d0.size), 32 ≤ q → q < 36 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 32 x4s5d0g32c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g36c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g36 : ∀ q (hq : q < x4s5d0.size), 36 ≤ q → q < 40 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 36 x4s5d0g36c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g40c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,0x180f,15,15,0x200f,15,0x280f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g40 : ∀ q (hq : q < x4s5d0.size), 40 ≤ q → q < 44 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 40 x4s5d0g40c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g44c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,0xe80f,15,0xc00f,15,0x980f,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g44 : ∀ q (hq : q < x4s5d0.size), 44 ≤ q → q < 48 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 44 x4s5d0g44c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g48c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g48 : ∀ q (hq : q < x4s5d0.size), 48 ≤ q → q < 52 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 48 x4s5d0g48c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g52c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g52 : ∀ q (hq : q < x4s5d0.size), 52 ≤ q → q < 56 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 52 x4s5d0g52c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g56c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,0x380f,15,0x400f,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g56 : ∀ q (hq : q < x4s5d0.size), 56 ≤ q → q < 60 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 56 x4s5d0g56c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g60c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,0x480f,15,0x500f,15,0x580f,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,0xa00f,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,0xc80f,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g60 : ∀ q (hq : q < x4s5d0.size), 60 ≤ q → q < 64 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 60 x4s5d0g60c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g64c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g64 : ∀ q (hq : q < x4s5d0.size), 64 ≤ q → q < 68 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 64 x4s5d0g64c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g68c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,0xd80f,15,15,15,15,0x600f],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g68 : ∀ q (hq : q < x4s5d0.size), 68 ≤ q → q < 72 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 68 x4s5d0g68c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g72c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,0x700f,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g72 : ∀ q (hq : q < x4s5d0.size), 72 ≤ q → q < 76 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 72 x4s5d0g72c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g76c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g76 : ∀ q (hq : q < x4s5d0.size), 76 ≤ q → q < 80 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 76 x4s5d0g76c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g80c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,0x680f,15],[]),([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g80 : ∀ q (hq : q < x4s5d0.size), 80 ≤ q → q < 84 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 80 x4s5d0g80c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
def x4s5d0g84c : List (List ℕ × List ℕ) := [([15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,0x300f,15,15,15,15,15,15,15,0x600f],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0g84 : ∀ q (hq : q < x4s5d0.size), 84 ≤ q → q < 85 → ¬ Reach x4s5d0[q].toFinset 5 0 0xeee8e8a0 := by
  have check : part x4s5d0 0xeee8e8a0 5 0 x4s4d0 #[] 84 x4s5d0g84c = true := by decide +kernel
  exact part_ok x4s4d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d0ok : correct x4s5d0 5 0 0xeee8e8a0 := by
  intro q hq
  have lim : q < 85 := hq
  by_cases atMid : q < 44
  ·
    by_cases atMid : q < 20
    ·
      by_cases atMid : q < 8
      ·
        by_cases atMid : q < 4
        ·
          exact x4s5d0g0 q hq (by omega) (by omega)
        ·
          exact x4s5d0g4 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 12
        ·
          exact x4s5d0g8 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 16
          ·
            exact x4s5d0g12 q hq (by omega) (by omega)
          ·
            exact x4s5d0g16 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 32
      ·
        by_cases atMid : q < 24
        ·
          exact x4s5d0g20 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 28
          ·
            exact x4s5d0g24 q hq (by omega) (by omega)
          ·
            exact x4s5d0g28 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 36
        ·
          exact x4s5d0g32 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 40
          ·
            exact x4s5d0g36 q hq (by omega) (by omega)
          ·
            exact x4s5d0g40 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 64
    ·
      by_cases atMid : q < 52
      ·
        by_cases atMid : q < 48
        ·
          exact x4s5d0g44 q hq (by omega) (by omega)
        ·
          exact x4s5d0g48 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 56
        ·
          exact x4s5d0g52 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 60
          ·
            exact x4s5d0g56 q hq (by omega) (by omega)
          ·
            exact x4s5d0g60 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 76
      ·
        by_cases atMid : q < 68
        ·
          exact x4s5d0g64 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 72
          ·
            exact x4s5d0g68 q hq (by omega) (by omega)
          ·
            exact x4s5d0g72 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 80
        ·
          exact x4s5d0g76 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 84
          ·
            exact x4s5d0g80 q hq (by omega) (by omega)
          ·
            exact x4s5d0g84 q hq (by omega) (by omega)
def x4s5d1 : Array (List Word) := #[[0x88888888,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,inputC,0xff000000,inputD,inputE],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xffffff00]]
def x4s5d1g0c : List (List ℕ × List ℕ) := [([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x1602d,0x1402d,0x1002d,0xc02d,0x802d,0x402d]),([7,0x6807,7,0x5007,7,0x4007,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x1582e,0x1402e,0x1002e,0xc02e,0x802e,0x402e]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x1502f,0x1402f,0x1002f,0xc02f,0x802f,0x402f]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14830,0x14030,0x10030,0xc030,0x8030,0x4030])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d1g0 : ∀ q (hq : q < x4s5d1.size), 0 ≤ q → q < 4 → ¬ Reach x4s5d1[q].toFinset 5 1 0xeee8e8a0 := by
  have check : part x4s5d1 0xeee8e8a0 5 1 x4s4d1 x4s5d0 0 x4s5d1g0c = true := by decide +kernel
  exact part_ok x4s4d1ok x4s5d0ok check
def x4s5d1g4c : List (List ℕ × List ℕ) := [([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14035,0x11835,0x10035,0xc035,0x8035,0x4035]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14036,0x11036,0x10036,0xc036,0x8036,0x4036]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14037,0x10837,0x10037,0xc037,0x8037,0x4037]),([7,7,7,7,7,7,7,7,7,7,7,7,7,0x807,7,0x1007,7,0x1807,7,7,7,7,7,7,7],[0x1403c,0x1003c,0xd83c,0xc03c,0x803c,0x403c])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d1g4 : ∀ q (hq : q < x4s5d1.size), 4 ≤ q → q < 8 → ¬ Reach x4s5d1[q].toFinset 5 1 0xeee8e8a0 := by
  have check : part x4s5d1 0xeee8e8a0 5 1 x4s4d1 x4s5d0 4 x4s5d1g4c = true := by decide +kernel
  exact part_ok x4s4d1ok x4s5d0ok check
def x4s5d1g8c : List (List ℕ × List ℕ) := [([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,0x4807,7,7,7,7,7],[0x1403d,0x1003d,0xd03d,0xc03d,0x803d,0x403d]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,0x5807,7,7,7,7,7],[0x1403e,0x1003e,0xc83e,0xc03e,0x803e,0x403e]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14043,0x10043,0xc043,0x9843,0x8043,0x4043]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14044,0x10044,0xc044,0x9044,0x8044,0x4044])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d1g8 : ∀ q (hq : q < x4s5d1.size), 8 ≤ q → q < 12 → ¬ Reach x4s5d1[q].toFinset 5 1 0xeee8e8a0 := by
  have check : part x4s5d1 0xeee8e8a0 5 1 x4s4d1 x4s5d0 8 x4s5d1g8c = true := by decide +kernel
  exact part_ok x4s4d1ok x4s5d0ok check
def x4s5d1g12c : List (List ℕ × List ℕ) := [([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,0x6007,7,7,7,7,0x2007],[0x14045,0x10045,0xc045,0x8845,0x8045,0x4045]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x1404a,0x1004a,0xc04a,0x804a,0x584a,0x404a]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,0x3007,7],[0x1404b,0x1004b,0xc04b,0x804b,0x504b,0x404b]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x1404c,0x1004c,0xc04c,0x804c,0x484c,0x404c])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d1g12 : ∀ q (hq : q < x4s5d1.size), 12 ≤ q → q < 16 → ¬ Reach x4s5d1[q].toFinset 5 1 0xeee8e8a0 := by
  have check : part x4s5d1 0xeee8e8a0 5 1 x4s4d1 x4s5d0 12 x4s5d1g12c = true := by decide +kernel
  exact part_ok x4s4d1ok x4s5d0ok check
def x4s5d1g16c : List (List ℕ × List ℕ) := [([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14051,0x10051,0xc051,0x8051,0x4051,0x1851]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,0x2807,7],[0x14052,0x10052,0xc052,0x8052,0x4052,0x1052]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],[0x14053,0x10053,0xc053,0x8053,0x4053,0x853]),([7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,0x2007],[0x14054,0x10054,0xc054,0x8054,0x4054,0x54])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d1g16 : ∀ q (hq : q < x4s5d1.size), 16 ≤ q → q < 20 → ¬ Reach x4s5d1[q].toFinset 5 1 0xeee8e8a0 := by
  have check : part x4s5d1 0xeee8e8a0 5 1 x4s4d1 x4s5d0 16 x4s5d1g16c = true := by decide +kernel
  exact part_ok x4s4d1ok x4s5d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s5d1ok : correct x4s5d1 5 1 0xeee8e8a0 := by
  intro q hq
  have lim : q < 20 := hq
  by_cases atMid : q < 8
  ·
    by_cases atMid : q < 4
    ·
      exact x4s5d1g0 q hq (by omega) (by omega)
    ·
      exact x4s5d1g4 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 12
    ·
      exact x4s5d1g8 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 16
      ·
        exact x4s5d1g12 q hq (by omega) (by omega)
      ·
        exact x4s5d1g16 q hq (by omega) (by omega)
def x4s6d0 : Array (List Word) := #[[0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE]]
def x4s6d0g0c : List (List ℕ × List ℕ) := [([0x2008,0x18808,0x2808,0x1c008,0x3008,0x1f808,0x3808,0x23008,0x16808,0x1e008,0x17008,0x21808,0x17808,0x25008,0x18008,0x28808,0x1a808,0x22008,0x1b008,0x25808,0x1b808,0x29008,0x1e808,0x26008,0x1f008,0x29808,0x22808,0x2a008],[]),([0x6010,0x19010,0x6810,0x1c810,0x7010,0x20010,0x7810,0x26810,0x16810,0x1e010,0x17010,0x21810,0x17810,0x25010,0x18010,0x28810,0x1a810,0x22010,0x1b010,0x25810,0x1b810,0x29010,0x1e810,0x26010,0x1f010,0x29810,0x22810,0x2a010],[]),([0xa018,0x19818,0xa818,0x1d018,0xb018,0x23818,0xb818,0x27018,0x16818,0x1e018,0x17018,0x21818,0x17818,0x25018,0x18018,0x28818,0x1a818,0x22018,0x1b018,0x25818,0x1b818,0x29018,0x1e818,0x26018,0x1f018,0x29818,0x22818,0x2a018],[]),([0xe020,0x1a020,0xe820,0x20820,0xf020,0x24020,0xf820,0x27820,0x16820,0x1e020,0x17020,0x21820,0x17820,0x25020,0x18020,0x28820,0x1a820,0x22020,0x1b020,0x25820,0x1b820,0x29020,0x1e820,0x26020,0x1f020,0x29820,0x22820,0x2a020],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s6d0g0 : ∀ q (hq : q < x4s6d0.size), 0 ≤ q → q < 4 → ¬ Reach x4s6d0[q].toFinset 6 0 0xeee8e8a0 := by
  have check : part x4s6d0 0xeee8e8a0 6 0 x4s5d0 #[] 0 x4s6d0g0c = true := by decide +kernel
  exact part_ok x4s5d0ok (noRows _ _ _) check
def x4s6d0g4c : List (List ℕ × List ℕ) := [([0x12028,0x1d828,0x12828,0x21028,0x13028,0x24828,0x13828,0x28028,0x16828,0x1e028,0x17028,0x21828,0x17828,0x25028,0x18028,0x28828,0x1a828,0x22028,0x1b028,0x25828,0x1b828,0x29028,0x1e828,0x26028,0x1f028,0x29828,0x22828,0x2a028],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s6d0g4 : ∀ q (hq : q < x4s6d0.size), 4 ≤ q → q < 5 → ¬ Reach x4s6d0[q].toFinset 6 0 0xeee8e8a0 := by
  have check : part x4s6d0 0xeee8e8a0 6 0 x4s5d0 #[] 4 x4s6d0g4c = true := by decide +kernel
  exact part_ok x4s5d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s6d0ok : correct x4s6d0 6 0 0xeee8e8a0 := by
  intro q hq
  have lim : q < 5 := hq
  by_cases atMid : q < 4
  ·
    exact x4s6d0g0 q hq (by omega) (by omega)
  ·
    exact x4s6d0g4 q hq (by omega) (by omega)
def x4s6d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x4s6d1g0c : List (List ℕ × List ℕ) := [([0,7,1,10,2,13,3,16,4,11,5,14,6,17,8,15,9,18,12,19],[4,3,2,1,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s6d1g0 : ∀ q (hq : q < x4s6d1.size), 0 ≤ q → q < 1 → ¬ Reach x4s6d1[q].toFinset 6 1 0xeee8e8a0 := by
  have check : part x4s6d1 0xeee8e8a0 6 1 x4s5d1 x4s6d0 0 x4s6d1g0c = true := by decide +kernel
  exact part_ok x4s5d1ok x4s6d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x4s6d1ok : correct x4s6d1 6 1 0xeee8e8a0 := by
  exact fun q hq => x4s6d1g0 q hq (Nat.zero_le _) hq
def x4gates : List Gate := [⟨.and, [3,4]⟩,⟨.or, [3,4]⟩,⟨.and, [1,6]⟩,⟨.and, [0,7]⟩,⟨.or, [0,7]⟩,⟨.or, [5,8]⟩,⟨.or, [2,10]⟩,⟨.and, [9,11]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result4 : Verdict 0xeee8e8a0 := by
  apply verdict (k := 6) (by decide) (by decide) (x4s6d1ok 0 (by decide)) x4gates 12
  · simp [x4gates,mono]
  · decide
  · decide +kernel

def x5maps : Array ShiftMap := #[([],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]),([(8,0xff00),(24,0xff0000)],[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]),([(4,0xf000f0),(28,0xf000f00)],[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]),([(4,0xf00000),(8,0xf000),(12,0xf0),(20,0xf000000),(24,0xf0000),(28,0xf00)],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]),([(4,0xf0),(8,0xf00),(12,0xf000),(20,0xf0000),(24,0xf00000),(28,0xf000000)],[0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31]),([(12,0xf0f0),(20,0xf0f0000)],[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31]),([(2,0xc0c0c0c),(30,0x30303030)],[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31]),([(2,0xc00000c),(6,0x3000),(8,0xc300),(10,0xc00),(22,0x300000),(24,0xc30000),(26,0xc0000),(30,0x30000030)],[0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31]),([(2,0xc000c00),(4,0xc000c0),(6,0xc000c),(26,0x30003000),(28,0x3000300),(30,0x300030)],[0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31]),([(2,0xc000000),(4,0xc00000),(6,0xc0000),(8,0xc000),(10,0xc00),(12,0xc0),(14,0xc),(18,0x30000000),(20,0x3000000),(22,0x300000),(24,0x30000),(26,0x3000),(28,0x300),(30,0x30)],[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]),([(2,0xc000000),(4,0xc0),(6,0x300c),(8,0x300),(12,0xc000),(14,0xc00),(18,0x300000),(20,0x30000),(24,0xc00000),(26,0x300c0000),(28,0x3000000),(30,0x30)],[0,1,4,5,16,17,20,21,2,3,6,7,18,19,22,23,8,9,12,13,24,25,28,29,10,11,14,15,26,27,30,31]),([(2,0xc0c0000),(12,0xc0c0),(14,0xc0c),(18,0x30300000),(20,0x3030000),(30,0x3030)],[0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,2,3,6,7,18,19,22,23,10,11,14,15,26,27,30,31]),([(2,0xc000c),(4,0x300030),(6,0xc000c0),(26,0x3000300),(28,0xc000c00),(30,0x30003000)],[0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31]),([(2,0xc),(4,0x300000),(6,0xc03000),(8,0xc000),(12,0x30),(14,0xc0),(18,0x3000000),(20,0xc000000),(24,0x30000),(26,0xc0300),(28,0xc00),(30,0x30000000)],[0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27,4,5,12,13,6,7,14,15,20,21,28,29,22,23,30,31]),([(6,0xcc00cc),(26,0x33003300)],[0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15,16,17,24,25,20,21,28,29,18,19,26,27,22,23,30,31]),([(6,0xcc0000),(8,0xcc00),(14,0xcc),(18,0x33000000),(24,0x330000),(26,0x3300)],[0,1,8,9,4,5,12,13,16,17,24,25,20,21,28,29,2,3,10,11,6,7,14,15,18,19,26,27,22,23,30,31]),([(6,0xc0300c),(12,0xc030),(14,0x3000000),(18,0xc0),(20,0xc030000),(26,0x300c0300)],[0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27,4,5,12,13,20,21,28,29,6,7,14,15,22,23,30,31]),([(2,0xc0000),(4,0x30),(6,0xc00000),(8,0xc00),(12,0xc000),(14,0x300000c),(18,0x300000c0),(20,0x30000),(24,0x300000),(26,0x300),(28,0xc000000),(30,0x3000)],[0,1,8,9,16,17,24,25,4,5,12,13,20,21,28,29,2,3,10,11,18,19,26,27,6,7,14,15,22,23,30,31]),([(2,0xc),(4,0x30),(6,0xc0),(8,0x300),(10,0xc00),(12,0x3000),(14,0xc000),(18,0x30000),(20,0xc0000),(22,0x300000),(24,0xc00000),(26,0x3000000),(28,0xc000000),(30,0x30000000)],[0,1,16,17,2,3,18,19,4,5,20,21,6,7,22,23,8,9,24,25,10,11,26,27,12,13,28,29,14,15,30,31]),([(2,0xc0c),(12,0x3030),(14,0xc0c0),(18,0x3030000),(20,0xc0c0000),(30,0x30300000)],[0,1,16,17,2,3,18,19,8,9,24,25,10,11,26,27,4,5,20,21,6,7,22,23,12,13,28,29,14,15,30,31]),([(6,0xcc),(8,0x3300),(14,0xcc00),(18,0x330000),(24,0xcc0000),(26,0x33000000)],[0,1,16,17,4,5,20,21,2,3,18,19,6,7,22,23,8,9,24,25,12,13,28,29,10,11,26,27,14,15,30,31]),([(14,0xcccc),(18,0x33330000)],[0,1,16,17,4,5,20,21,8,9,24,25,12,13,28,29,2,3,18,19,6,7,22,23,10,11,26,27,14,15,30,31]),([(2,0xc00),(4,0xc00000),(6,0xc),(8,0x3000),(12,0x30),(14,0x300c000),(18,0x300c0),(20,0xc000000),(24,0xc0000),(26,0x30000000),(28,0x300),(30,0x300000)],[0,1,16,17,8,9,24,25,2,3,18,19,10,11,26,27,4,5,20,21,12,13,28,29,6,7,22,23,14,15,30,31]),([(4,0xc00030),(10,0xc00),(14,0x300c00c),(18,0x300300c0),(22,0x300000),(28,0xc000300)],[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,2,3,18,19,10,11,26,27,6,7,22,23,14,15,30,31]),([(1,0x22222222),(31,0x44444444)],[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31]),([(1,0x22000022),(7,0x4400),(8,0x9900),(9,0x2200),(23,0x440000),(24,0x990000),(25,0x220000),(31,0x44000044)],[0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31]),([(1,0x20022002),(3,0x400040),(4,0x900090),(5,0x200020),(27,0x4000400),(28,0x9000900),(29,0x2000200),(31,0x40044004)],[0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]),([(1,0x20000002),(3,0x400000),(4,0x900000),(5,0x200000),(7,0x4000),(8,0x9000),(9,0x2000),(11,0x40),(12,0x90),(13,0x20),(19,0x4000000),(20,0x9000000),(21,0x2000000),(23,0x40000),(24,0x90000),(25,0x20000),(27,0x400),(28,0x900),(29,0x200),(31,0x40000004)],[0,2,1,3,8,10,9,11,16,18,17,19,24,26,25,27,4,6,5,7,12,14,13,15,20,22,21,23,28,30,29,31]),([(1,0x20000002),(3,0x40),(4,0x90),(5,0x20),(7,0x400),(8,0x900),(9,0x200),(11,0x4000),(12,0x9000),(13,0x2000),(19,0x40000),(20,0x90000),(21,0x20000),(23,0x400000),(24,0x900000),(25,0x200000),(27,0x4000000),(28,0x9000000),(29,0x2000000),(31,0x40000004)],[0,2,1,3,16,18,17,19,4,6,5,7,20,22,21,23,8,10,9,11,24,26,25,27,12,14,13,15,28,30,29,31]),([(1,0x20200202),(11,0x4040),(12,0x9090),(13,0x2020),(19,0x4040000),(20,0x9090000),(21,0x2020000),(31,0x40400404)],[0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31]),([(1,0x20202020),(2,0x8080808),(3,0x2020202),(29,0x40404040),(30,0x10101010),(31,0x4040404)],[0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31]),([(1,0x20000020),(2,0x8000008),(3,0x2000002),(5,0x4000),(6,0x1000),(7,0x400),(8,0x8100),(9,0x2000),(10,0x800),(11,0x200),(21,0x400000),(22,0x100000),(23,0x40000),(24,0x810000),(25,0x200000),(26,0x80000),(27,0x20000),(29,0x40000040),(30,0x10000010),(31,0x4000004)],[0,2,4,6,1,3,5,7,16,18,20,22,17,19,21,23,8,10,12,14,9,11,13,15,24,26,28,30,25,27,29,31]),([(1,0x20002000),(2,0x8000800),(3,0x2000200),(4,0x800080),(5,0x200020),(6,0x80008),(7,0x20002),(25,0x40004000),(26,0x10001000),(27,0x4000400),(28,0x1000100),(29,0x400040),(30,0x100010),(31,0x40004)],[0,2,4,6,8,10,12,14,1,3,5,7,9,11,13,15,16,18,20,22,24,26,28,30,17,19,21,23,25,27,29,31]),([(1,0x20000000),(2,0x8000000),(3,0x2000000),(4,0x800000),(5,0x200000),(6,0x80000),(7,0x20000),(8,0x8000),(9,0x2000),(10,0x800),(11,0x200),(12,0x80),(13,0x20),(14,0x8),(15,0x2),(17,0x40000000),(18,0x10000000),(19,0x4000000),(20,0x1000000),(21,0x400000),(22,0x100000),(23,0x40000),(24,0x10000),(25,0x4000),(26,0x1000),(27,0x400),(28,0x100),(29,0x40),(30,0x10),(31,0x4)],[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31]),([(1,0x20000000),(2,0x8000000),(3,0x2000000),(4,0x80),(5,0x4020),(6,0x1008),(7,0x402),(8,0x100),(12,0x8000),(13,0x2000),(14,0x800),(15,0x200),(17,0x400000),(18,0x100000),(19,0x40000),(20,0x10000),(24,0x800000),(25,0x40200000),(26,0x10080000),(27,0x4020000),(28,0x1000000),(29,0x40),(30,0x10),(31,0x4)],[0,2,4,6,16,18,20,22,1,3,5,7,17,19,21,23,8,10,12,14,24,26,28,30,9,11,13,15,25,27,29,31]),([(1,0x20200000),(2,0x8080000),(3,0x2020000),(12,0x8080),(13,0x2020),(14,0x808),(15,0x202),(17,0x40400000),(18,0x10100000),(19,0x4040000),(20,0x1010000),(29,0x4040),(30,0x1010),(31,0x404)],[0,2,4,6,16,18,20,22,8,10,12,14,24,26,28,30,1,3,5,7,17,19,21,23,9,11,13,15,25,27,29,31]),([(1,0x20002000),(2,0x80008),(3,0x420042),(4,0x100010),(6,0x800080),(7,0x200020),(25,0x4000400),(26,0x1000100),(28,0x8000800),(29,0x42004200),(30,0x10001000),(31,0x40004)],[0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15,16,18,24,26,17,19,25,27,20,22,28,30,21,23,29,31]),([(1,0x20000000),(2,0x8),(3,0x400002),(4,0x100000),(5,0x4000),(6,0x801000),(7,0x200000),(8,0x8000),(9,0x2000),(11,0x40),(12,0x10),(14,0x80),(15,0x20),(17,0x4000000),(18,0x1000000),(20,0x8000000),(21,0x2000000),(23,0x40000),(24,0x10000),(25,0x400),(26,0x80100),(27,0x20000),(28,0x800),(29,0x40000200),(30,0x10000000),(31,0x4)],[0,2,8,10,1,3,9,11,16,18,24,26,17,19,25,27,4,6,12,14,5,7,13,15,20,22,28,30,21,23,29,31]),([(1,0x22002200),(6,0x880088),(7,0x220022),(25,0x44004400),(26,0x11001100),(31,0x440044)],[0,2,8,10,4,6,12,14,1,3,9,11,5,7,13,15,16,18,24,26,20,22,28,30,17,19,25,27,21,23,29,31]),([(1,0x22000000),(6,0x880000),(7,0x220000),(8,0x8800),(9,0x2200),(14,0x88),(15,0x22),(17,0x44000000),(18,0x11000000),(23,0x440000),(24,0x110000),(25,0x4400),(26,0x1100),(31,0x44)],[0,2,8,10,4,6,12,14,16,18,24,26,20,22,28,30,1,3,9,11,5,7,13,15,17,19,25,27,21,23,29,31]),([(1,0x20000200),(5,0x4000),(6,0x801008),(7,0x200002),(11,0x40),(12,0x8010),(13,0x4002000),(14,0x1000000),(18,0x80),(19,0x40020),(20,0x8010000),(21,0x2000000),(25,0x40000400),(26,0x10080100),(27,0x20000),(31,0x400004)],[0,2,8,10,16,18,24,26,1,3,9,11,17,19,25,27,4,6,12,14,20,22,28,30,5,7,13,15,21,23,29,31]),([(1,0x20000000),(2,0x80000),(3,0x20040),(4,0x10),(6,0x800000),(7,0x200000),(8,0x800),(9,0x200),(12,0x8000),(13,0x4002000),(14,0x1000008),(15,0x2),(17,0x40000000),(18,0x10000080),(19,0x40020),(20,0x10000),(23,0x400000),(24,0x100000),(25,0x400),(26,0x100),(28,0x8000000),(29,0x2004000),(30,0x1000),(31,0x4)],[0,2,8,10,16,18,24,26,4,6,12,14,20,22,28,30,1,3,9,11,17,19,25,27,5,7,13,15,21,23,29,31]),([(1,0x20000000),(2,0x8),(3,0x42),(4,0x10),(6,0x80),(7,0x420),(8,0x100),(10,0x800),(11,0x4200),(12,0x1000),(14,0x8000),(15,0x2000),(17,0x40000),(18,0x10000),(20,0x80000),(21,0x420000),(22,0x100000),(24,0x800000),(25,0x4200000),(26,0x1000000),(28,0x8000000),(29,0x42000000),(30,0x10000000),(31,0x4)],[0,2,16,18,1,3,17,19,4,6,20,22,5,7,21,23,8,10,24,26,9,11,25,27,12,14,28,30,13,15,29,31]),([(1,0x20200000),(2,0x808),(3,0x202),(11,0x4040),(12,0x1010),(14,0x8080),(15,0x2020),(17,0x4040000),(18,0x1010000),(20,0x8080000),(21,0x2020000),(29,0x40400000),(30,0x10100000),(31,0x404)],[0,2,16,18,1,3,17,19,8,10,24,26,9,11,25,27,4,6,20,22,5,7,21,23,12,14,28,30,13,15,29,31]),([(1,0x22000000),(6,0x88),(7,0x4422),(8,0x1100),(14,0x8800),(15,0x2200),(17,0x440000),(18,0x110000),(24,0x880000),(25,0x44220000),(26,0x11000000),(31,0x44)],[0,2,16,18,4,6,20,22,1,3,17,19,5,7,21,23,8,10,24,26,12,14,28,30,9,11,25,27,13,15,29,31]),([(1,0x22220000),(14,0x8888),(15,0x2222),(17,0x44440000),(18,0x11110000),(31,0x4444)],[0,2,16,18,4,6,20,22,8,10,24,26,12,14,28,30,1,3,17,19,5,7,21,23,9,11,25,27,13,15,29,31]),([(1,0x20000000),(2,0x800),(3,0x200),(4,0x800000),(5,0x200000),(6,0x8),(7,0x4002),(8,0x1000),(11,0x40),(12,0x10),(13,0x4000000),(14,0x1008000),(15,0x2000),(17,0x40000),(18,0x10080),(19,0x20),(20,0x8000000),(21,0x2000000),(24,0x80000),(25,0x40020000),(26,0x10000000),(27,0x400),(28,0x100),(29,0x400000),(30,0x100000),(31,0x4)],[0,2,16,18,8,10,24,26,1,3,17,19,9,11,25,27,4,6,20,22,12,14,28,30,5,7,21,23,13,15,29,31]),([(1,0x20020000),(3,0x40),(4,0x800010),(5,0x200000),(10,0x800),(11,0x200),(13,0x4000000),(14,0x1008008),(15,0x2002),(17,0x40040000),(18,0x10010080),(19,0x20),(21,0x400000),(22,0x100000),(27,0x400),(28,0x8000100),(29,0x2000000),(31,0x4004)],[0,2,16,18,8,10,24,26,4,6,20,22,12,14,28,30,1,3,17,19,9,11,25,27,5,7,21,23,13,15,29,31]),([(1,0x2020202),(2,0x4040404),(3,0x8080808),(29,0x10101010),(30,0x20202020),(31,0x40404040)],[0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31]),([(1,0x2000002),(2,0x4000004),(3,0x8000008),(5,0x1000),(6,0x2000),(7,0x4000),(8,0x8100),(9,0x200),(10,0x400),(11,0x800),(21,0x100000),(22,0x200000),(23,0x400000),(24,0x810000),(25,0x20000),(26,0x40000),(27,0x80000),(29,0x10000010),(30,0x20000020),(31,0x40000040)],[0,4,1,5,2,6,3,7,16,20,17,21,18,22,19,23,8,12,9,13,10,14,11,15,24,28,25,29,26,30,27,31]),([(1,0x20002),(2,0x4000400),(3,0x8400840),(4,0x800080),(6,0x40004),(7,0x80008),(25,0x10001000),(26,0x20002000),(28,0x1000100),(29,0x2100210),(30,0x200020),(31,0x40004000)],[0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15,16,20,17,21,24,28,25,29,18,22,19,23,26,30,27,31]),([(1,0x2),(2,0x4000000),(3,0x8400000),(4,0x800000),(6,0x40000),(7,0x84000),(8,0x8000),(10,0x400),(11,0x840),(12,0x80),(14,0x4),(15,0x8),(17,0x10000000),(18,0x20000000),(20,0x1000000),(21,0x2100000),(22,0x200000),(24,0x10000),(25,0x21000),(26,0x2000),(28,0x100),(29,0x210),(30,0x20),(31,0x40000000)],[0,4,1,5,8,12,9,13,16,20,17,21,24,28,25,29,2,6,3,7,10,14,11,15,18,22,19,23,26,30,27,31]),([(1,0x2),(2,0x4000000),(3,0x8000040),(4,0x80),(5,0x1000),(6,0x2004),(7,0x8),(8,0x100),(9,0x200),(11,0x4000),(12,0x8000),(14,0x400),(15,0x800),(17,0x100000),(18,0x200000),(20,0x10000),(21,0x20000),(23,0x400000),(24,0x800000),(25,0x10000000),(26,0x20040000),(27,0x80000),(28,0x1000000),(29,0x2000010),(30,0x20),(31,0x40000000)],[0,4,1,5,16,20,17,21,2,6,3,7,18,22,19,23,8,12,9,13,24,28,25,29,10,14,11,15,26,30,27,31]),([(1,0x202),(2,0x4040000),(3,0x8080000),(11,0x4040),(12,0x8080),(14,0x404),(15,0x808),(17,0x10100000),(18,0x20200000),(20,0x1010000),(21,0x2020000),(29,0x1010),(30,0x2020),(31,0x40400000)],[0,4,1,5,16,20,17,21,8,12,9,13,24,28,25,29,2,6,3,7,18,22,19,23,10,14,11,15,26,30,27,31]),([(3,0xa0a0a0a),(29,0x50505050)],[0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15,16,20,18,22,17,21,19,23,24,28,26,30,25,29,27,31]),([(3,0xa00000a),(5,0x5000),(8,0xa500),(11,0xa00),(21,0x500000),(24,0xa50000),(27,0xa0000),(29,0x50000050)],[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23,8,12,10,14,9,13,11,15,24,28,26,30,25,29,27,31]),([(3,0xa000a00),(4,0xa000a0),(7,0xa000a),(25,0x50005000),(28,0x5000500),(29,0x500050)],[0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15,16,20,18,22,24,28,26,30,17,21,19,23,25,29,27,31]),([(3,0xa000000),(4,0xa00000),(7,0xa0000),(8,0xa000),(11,0xa00),(12,0xa0),(15,0xa),(17,0x50000000),(20,0x5000000),(21,0x500000),(24,0x50000),(25,0x5000),(28,0x500),(29,0x50)],[0,4,2,6,8,12,10,14,16,20,18,22,24,28,26,30,1,5,3,7,9,13,11,15,17,21,19,23,25,29,27,31]),([(3,0xa000000),(4,0xa0),(5,0x5000),(7,0xa),(8,0x500),(12,0xa000),(15,0xa00),(17,0x500000),(20,0x50000),(24,0xa00000),(25,0x50000000),(27,0xa0000),(28,0x5000000),(29,0x50)],[0,4,2,6,16,20,18,22,1,5,3,7,17,21,19,23,8,12,10,14,24,28,26,30,9,13,11,15,25,29,27,31]),([(3,0xa0a0000),(12,0xa0a0),(15,0xa0a),(17,0x50500000),(20,0x5050000),(29,0x5050)],[0,4,2,6,16,20,18,22,8,12,10,14,24,28,26,30,1,5,3,7,17,21,19,23,9,13,11,15,25,29,27,31]),([(3,0x8420842),(6,0x840084),(9,0x80008),(23,0x10001000),(26,0x21002100),(29,0x42104210)],[0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15,16,20,24,28,17,21,25,29,18,22,26,30,19,23,27,31]),([(3,0x8400002),(5,0x4000),(6,0x840000),(8,0x8400),(9,0x80000),(11,0x840),(14,0x84),(15,0x10000000),(17,0x8),(18,0x21000000),(21,0x2100000),(23,0x1000),(24,0x210000),(26,0x2100),(27,0x20000),(29,0x40000210)],[0,4,8,12,1,5,9,13,16,20,24,28,17,21,25,29,2,6,10,14,3,7,11,15,18,22,26,30,19,23,27,31]),([(1,0x2000200),(2,0x40004),(3,0x8000800),(4,0x200020),(6,0x800080),(7,0x20002),(9,0x80008),(23,0x10001000),(25,0x40004000),(26,0x1000100),(28,0x4000400),(29,0x100010),(30,0x20002000),(31,0x400040)],[0,4,8,12,2,6,10,14,1,5,9,13,3,7,11,15,16,20,24,28,18,22,26,30,17,21,25,29,19,23,27,31]),([(1,0x2000000),(2,0x4),(3,0x8000000),(4,0x200000),(6,0x802000),(7,0x20000),(8,0x8000),(9,0x80200),(11,0x800),(12,0x20),(14,0x80),(15,0x10000002),(17,0x40000008),(18,0x1000000),(20,0x4000000),(21,0x100000),(23,0x401000),(24,0x10000),(25,0x4000),(26,0x40100),(28,0x400),(29,0x10),(30,0x20000000),(31,0x40)],[0,4,8,12,2,6,10,14,16,20,24,28,18,22,26,30,1,5,9,13,3,7,11,15,17,21,25,29,19,23,27,31]),([(1,0x200),(2,0x40000),(3,0x8000000),(4,0x20),(5,0x4000),(6,0x800000),(7,0x2),(8,0x400),(9,0x80000),(11,0x10000040),(12,0x8000),(14,0x1000004),(15,0x800),(17,0x100000),(18,0x20000080),(20,0x10000),(21,0x2000008),(23,0x1000),(24,0x200000),(25,0x40000000),(26,0x100),(27,0x20000),(28,0x4000000),(29,0x10),(30,0x2000),(31,0x400000)],[0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,2,6,10,14,18,22,26,30,3,7,11,15,19,23,27,31]),([(3,0x8020040),(6,0x802004),(9,0x80200),(11,0x10000000),(12,0x8020),(14,0x1000000),(15,0x802),(17,0x40100000),(18,0x80),(20,0x4010000),(21,0x8),(23,0x401000),(26,0x20040100),(29,0x2004010)],[0,4,8,12,16,20,24,28,2,6,10,14,18,22,26,30,1,5,9,13,17,21,25,29,3,7,11,15,19,23,27,31]),([(3,0x8000042),(5,0x1000),(6,0x84),(8,0x2100),(9,0x8),(11,0x4200),(14,0x8400),(15,0x100000),(17,0x800),(18,0x210000),(21,0x420000),(23,0x10000000),(24,0x840000),(26,0x21000000),(27,0x80000),(29,0x42000010)],[0,4,16,20,1,5,17,21,2,6,18,22,3,7,19,23,8,12,24,28,9,13,25,29,10,14,26,30,11,15,27,31]),([(3,0x8080202),(11,0x4040),(14,0x8484),(15,0x10100000),(17,0x808),(18,0x21210000),(21,0x2020000),(29,0x40401010)],[0,4,16,20,1,5,17,21,8,12,24,28,9,13,25,29,2,6,18,22,3,7,19,23,10,14,26,30,11,15,27,31]),([(1,0x2000000),(2,0x4),(3,0x8000000),(4,0x20),(5,0x1000),(6,0x80),(7,0x4002),(8,0x100),(9,0x8),(10,0x400),(12,0x2000),(14,0x8000),(15,0x100200),(17,0x400800),(18,0x10000),(20,0x40000),(22,0x200000),(23,0x10000000),(24,0x800000),(25,0x40020000),(26,0x1000000),(27,0x80000),(28,0x4000000),(29,0x10),(30,0x20000000),(31,0x40)],[0,4,16,20,2,6,18,22,1,5,17,21,3,7,19,23,8,12,24,28,10,14,26,30,9,13,25,29,11,15,27,31]),([(1,0x2020000),(2,0x404),(3,0x8080000),(12,0x2020),(14,0x8080),(15,0x10100202),(17,0x40400808),(18,0x1010000),(20,0x4040000),(29,0x1010),(30,0x20200000),(31,0x4040)],[0,4,16,20,2,6,18,22,8,12,24,28,10,14,26,30,1,5,17,21,3,7,19,23,9,13,25,29,11,15,27,31]),([(3,0x8000200),(4,0x800020),(7,0x84002),(10,0x400),(11,0x10000040),(14,0x1008004),(15,0x100000),(17,0x800),(18,0x20010080),(21,0x2000008),(22,0x200000),(25,0x40021000),(28,0x4000100),(29,0x400010)],[0,4,16,20,8,12,24,28,1,5,17,21,9,13,25,29,2,6,18,22,10,14,26,30,3,7,19,23,11,15,27,31]),([(1,0x20000),(2,0x400),(3,0x8000040),(4,0x800000),(6,0x4),(7,0x80000),(8,0x2000),(11,0x10000200),(12,0x20),(14,0x1008000),(15,0x100002),(17,0x40000800),(18,0x10080),(20,0x4000000),(21,0x400008),(24,0x40000),(25,0x1000),(26,0x20000000),(28,0x100),(29,0x2000010),(30,0x200000),(31,0x4000)],[0,4,16,20,8,12,24,28,2,6,18,22,10,14,26,30,1,5,17,21,9,13,25,29,3,7,19,23,11,15,27,31]),([(1,0x20002),(2,0x40004),(3,0x80008),(4,0x100010),(5,0x200020),(6,0x400040),(7,0x800080),(25,0x1000100),(26,0x2000200),(27,0x4000400),(28,0x8000800),(29,0x10001000),(30,0x20002000),(31,0x40004000)],[0,8,1,9,2,10,3,11,4,12,5,13,6,14,7,15,16,24,17,25,18,26,19,27,20,28,21,29,22,30,23,31]),([(1,0x2),(2,0x4),(3,0x8),(4,0x100000),(5,0x201000),(6,0x402000),(7,0x804000),(8,0x8000),(12,0x10),(13,0x20),(14,0x40),(15,0x80),(17,0x1000000),(18,0x2000000),(19,0x4000000),(20,0x8000000),(24,0x10000),(25,0x20100),(26,0x40200),(27,0x80400),(28,0x800),(29,0x10000000),(30,0x20000000),(31,0x40000000)],[0,8,1,9,2,10,3,11,16,24,17,25,18,26,19,27,4,12,5,13,6,14,7,15,20,28,21,29,22,30,23,31]),([(1,0x220022),(6,0x440044),(7,0x880088),(25,0x11001100),(26,0x22002200),(31,0x44004400)],[0,8,1,9,4,12,5,13,2,10,3,11,6,14,7,15,16,24,17,25,20,28,21,29,18,26,19,27,22,30,23,31]),([(1,0x22),(6,0x440000),(7,0x884400),(8,0x8800),(14,0x44),(15,0x88),(17,0x11000000),(18,0x22000000),(24,0x110000),(25,0x221100),(26,0x2200),(31,0x44000000)],[0,8,1,9,4,12,5,13,16,24,17,25,20,28,21,29,2,10,3,11,6,14,7,15,18,26,19,27,22,30,23,31]),([(1,0x200002),(5,0x1000),(6,0x402004),(7,0x800008),(11,0x4000),(12,0x8010),(13,0x1000020),(14,0x2000000),(18,0x40),(19,0x4000080),(20,0x8010000),(21,0x20000),(25,0x10000100),(26,0x20040200),(27,0x80000),(31,0x40000400)],[0,8,1,9,16,24,17,25,2,10,3,11,18,26,19,27,4,12,5,13,20,28,21,29,6,14,7,15,22,30,23,31]),([(1,0x2),(2,0x40000),(3,0x80000),(4,0x10),(5,0x20),(6,0x400000),(7,0x800400),(8,0x800),(11,0x4000),(12,0x8000),(13,0x1000000),(14,0x2000004),(15,0x8),(17,0x10000000),(18,0x20000040),(19,0x80),(20,0x10000),(21,0x20000),(24,0x100000),(25,0x200100),(26,0x200),(27,0x4000000),(28,0x8000000),(29,0x1000),(30,0x2000),(31,0x40000000)],[0,8,1,9,16,24,17,25,4,12,5,13,20,28,21,29,2,10,3,11,18,26,19,27,6,14,7,15,22,30,23,31]),([(3,0xa000a),(4,0x500050),(7,0xa000a0),(25,0x5000500),(28,0xa000a00),(29,0x50005000)],[0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15,16,24,18,26,17,25,19,27,20,28,22,30,21,29,23,31]),([(3,0xa),(4,0x500000),(5,0x5000),(7,0xa00000),(8,0xa000),(12,0x50),(15,0xa0),(17,0x5000000),(20,0xa000000),(24,0x50000),(25,0x500),(27,0xa0000),(28,0xa00),(29,0x50000000)],[0,8,2,10,1,9,3,11,16,24,18,26,17,25,19,27,4,12,6,14,5,13,7,15,20,28,22,30,21,29,23,31]),([(7,0xaa00aa),(25,0x55005500)],[0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15,16,24,18,26,20,28,22,30,17,25,19,27,21,29,23,31]),([(7,0xaa0000),(8,0xaa00),(15,0xaa),(17,0x55000000),(24,0x550000),(25,0x5500)],[0,8,2,10,4,12,6,14,16,24,18,26,20,28,22,30,1,9,3,11,5,13,7,15,17,25,19,27,21,29,23,31]),([(5,0x5000),(7,0xa0000a),(12,0xa050),(13,0x5000000),(19,0xa0),(20,0xa050000),(25,0x50000500),(27,0xa0000)],[0,8,2,10,16,24,18,26,1,9,3,11,17,25,19,27,4,12,6,14,20,28,22,30,5,13,7,15,21,29,23,31]),([(3,0xa0000),(4,0x50),(7,0xa00000),(8,0xa00),(12,0xa000),(13,0x5000000),(15,0xa),(17,0x50000000),(19,0xa0),(20,0x50000),(24,0x500000),(25,0x500),(28,0xa000000),(29,0x5000)],[0,8,2,10,16,24,18,26,4,12,6,14,20,28,22,30,1,9,3,11,17,25,19,27,5,13,7,15,21,29,23,31]),([(1,0x200020),(2,0x8000800),(3,0x20002),(4,0x400040),(6,0x40004),(7,0x800080),(9,0x80008),(23,0x10001000),(25,0x1000100),(26,0x20002000),(28,0x2000200),(29,0x40004000),(30,0x100010),(31,0x4000400)],[0,8,4,12,1,9,5,13,2,10,6,14,3,11,7,15,16,24,20,28,17,25,21,29,18,26,22,30,19,27,23,31]),([(1,0x20),(2,0x8000000),(3,0x2),(4,0x400000),(5,0x4000),(6,0x40000),(7,0x800400),(8,0x8000),(9,0x80000),(10,0x800),(12,0x40),(14,0x4),(15,0x10000080),(17,0x1000008),(18,0x20000000),(20,0x2000000),(22,0x100000),(23,0x1000),(24,0x10000),(25,0x200100),(26,0x2000),(27,0x20000),(28,0x200),(29,0x40000000),(30,0x10),(31,0x4000000)],[0,8,4,12,1,9,5,13,16,24,20,28,17,25,21,29,2,10,6,14,3,11,7,15,18,26,22,30,19,27,23,31]),([(2,0x8040804),(5,0x200020),(7,0x820082),(9,0x80008),(23,0x10001000),(25,0x41004100),(27,0x4000400),(30,0x20102010)],[0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15,16,24,20,28,18,26,22,30,17,25,21,29,19,27,23,31]),([(2,0x8000004),(5,0x200000),(6,0x2000),(7,0x820000),(8,0x8200),(9,0x80000),(10,0x800),(13,0x20),(15,0x10000082),(17,0x41000008),(19,0x4000000),(22,0x100000),(23,0x1000),(24,0x410000),(25,0x4100),(26,0x40000),(27,0x400),(30,0x20000010)],[0,8,4,12,2,10,6,14,16,24,20,28,18,26,22,30,1,9,5,13,3,11,7,15,17,25,21,29,19,27,23,31]),([(2,0x8040000),(5,0x4020),(7,0x800402),(9,0x80000),(11,0x10000000),(12,0x8040),(13,0x1000000),(14,0x804),(18,0x20100000),(19,0x80),(20,0x2010000),(21,0x8),(23,0x1000),(25,0x40200100),(27,0x4020000),(30,0x2010)],[0,8,4,12,16,24,20,28,1,9,5,13,17,25,21,29,2,10,6,14,18,26,22,30,3,11,7,15,19,27,23,31]),([(1,0x200000),(2,0x8000000),(3,0x20000),(4,0x40),(6,0x2004),(7,0x800000),(8,0x200),(9,0x80000),(11,0x10000000),(12,0x8000),(13,0x1000020),(14,0x800),(15,0x2),(17,0x40000000),(18,0x100000),(19,0x4000080),(20,0x10000),(21,0x8),(23,0x1000),(24,0x400000),(25,0x100),(26,0x20040000),(28,0x2000000),(29,0x4000),(30,0x10),(31,0x400)],[0,8,4,12,16,24,20,28,2,10,6,14,18,26,22,30,1,9,5,13,17,25,21,29,3,11,7,15,19,27,23,31]),([(1,0x200000),(2,0x800),(3,0x2),(4,0x400000),(5,0x1000),(6,0x4),(7,0x800000),(8,0x2000),(9,0x8),(11,0x1004000),(12,0x10),(14,0x2008000),(15,0x20),(17,0x4000000),(18,0x10040),(20,0x8000000),(21,0x20080),(23,0x10000000),(24,0x40000),(25,0x100),(26,0x20000000),(27,0x80000),(28,0x200),(29,0x40000000),(30,0x100000),(31,0x400)],[0,8,16,24,1,9,17,25,2,10,18,26,3,11,19,27,4,12,20,28,5,13,21,29,6,14,22,30,7,15,23,31]),([(3,0x80002),(4,0x400010),(7,0x800420),(10,0x800),(11,0x1004000),(14,0x2008004),(15,0x10000000),(17,0x8),(18,0x20010040),(21,0x20080),(22,0x100000),(25,0x4200100),(28,0x8000200),(29,0x40001000)],[0,8,16,24,1,9,17,25,4,12,20,28,5,13,21,29,2,10,18,26,3,11,19,27,6,14,22,30,7,15,23,31]),([(2,0x804),(5,0x201000),(7,0x804002),(9,0x8),(11,0x1000000),(12,0x2010),(13,0x4000000),(14,0x8040),(18,0x2010000),(19,0x20),(20,0x8040000),(21,0x80),(23,0x10000000),(25,0x40020100),(27,0x80400),(30,0x20100000)],[0,8,16,24,2,10,18,26,1,9,17,25,3,11,19,27,4,12,20,28,6,14,22,30,5,13,21,29,7,15,23,31]),([(1,0x20000),(2,0x4),(3,0x80000),(4,0x10),(5,0x200000),(6,0x40),(7,0x800000),(8,0x200),(10,0x800),(11,0x1000000),(12,0x2000),(13,0x4000000),(14,0x8000),(15,0x10000002),(17,0x40000008),(18,0x10000),(19,0x20),(20,0x40000),(21,0x80),(22,0x100000),(24,0x400000),(25,0x100),(26,0x2000000),(27,0x400),(28,0x8000000),(29,0x1000),(30,0x20000000),(31,0x4000)],[0,8,16,24,2,10,18,26,4,12,20,28,6,14,22,30,1,9,17,25,3,11,19,27,5,13,21,29,7,15,23,31]),([(7,0x884422),(11,0x11000000),(14,0x8844),(18,0x22110000),(21,0x88),(25,0x44221100)],[0,8,16,24,4,12,20,28,1,9,17,25,5,13,21,29,2,10,18,26,6,14,22,30,3,11,19,27,7,15,23,31]),([(1,0x220000),(6,0x44),(7,0x880000),(8,0x2200),(11,0x11000000),(14,0x8800),(15,0x22),(17,0x44000000),(18,0x110000),(21,0x88),(24,0x440000),(25,0x1100),(26,0x22000000),(31,0x4400)],[0,8,16,24,4,12,20,28,2,10,18,26,6,14,22,30,1,9,17,25,5,13,21,29,3,11,19,27,7,15,23,31]),([(1,0x2),(2,0x4),(3,0x8),(4,0x10),(5,0x20),(6,0x40),(7,0x80),(8,0x100),(9,0x200),(10,0x400),(11,0x800),(12,0x1000),(13,0x2000),(14,0x4000),(15,0x8000),(17,0x10000),(18,0x20000),(19,0x40000),(20,0x80000),(21,0x100000),(22,0x200000),(23,0x400000),(24,0x800000),(25,0x1000000),(26,0x2000000),(27,0x4000000),(28,0x8000000),(29,0x10000000),(30,0x20000000),(31,0x40000000)],[0,16,1,17,2,18,3,19,4,20,5,21,6,22,7,23,8,24,9,25,10,26,11,27,12,28,13,29,14,30,15,31]),([(1,0x202),(2,0x404),(3,0x808),(12,0x1010),(13,0x2020),(14,0x4040),(15,0x8080),(17,0x1010000),(18,0x2020000),(19,0x4040000),(20,0x8080000),(29,0x10100000),(30,0x20200000),(31,0x40400000)],[0,16,1,17,2,18,3,19,8,24,9,25,10,26,11,27,4,20,5,21,6,22,7,23,12,28,13,29,14,30,15,31]),([(1,0x22),(6,0x44),(7,0x88),(8,0x1100),(9,0x2200),(14,0x4400),(15,0x8800),(17,0x110000),(18,0x220000),(23,0x440000),(24,0x880000),(25,0x11000000),(26,0x22000000),(31,0x44000000)],[0,16,1,17,4,20,5,21,2,18,3,19,6,22,7,23,8,24,9,25,12,28,13,29,10,26,11,27,14,30,15,31]),([(1,0x2222),(14,0x4444),(15,0x8888),(17,0x11110000),(18,0x22220000),(31,0x44440000)],[0,16,1,17,4,20,5,21,8,24,9,25,12,28,13,29,2,18,3,19,6,22,7,23,10,26,11,27,14,30,15,31]),([(1,0x2),(2,0x400),(3,0x400800),(4,0x800000),(6,0x4),(7,0x8),(8,0x1000),(9,0x2000),(12,0x10),(13,0x1000020),(14,0x2004000),(15,0x8000),(17,0x10000),(18,0x20040),(19,0x4000080),(20,0x8000000),(23,0x40000),(24,0x80000),(25,0x10000000),(26,0x20000000),(28,0x100),(29,0x100200),(30,0x200000),(31,0x40000000)],[0,16,1,17,8,24,9,25,2,18,3,19,10,26,11,27,4,20,5,21,12,28,13,29,6,22,7,23,14,30,15,31]),([(1,0x2002),(3,0x400000),(4,0x800010),(5,0x20),(10,0x400),(11,0x800),(13,0x1000000),(14,0x2004004),(15,0x8008),(17,0x10010000),(18,0x20020040),(19,0x80),(21,0x100000),(22,0x200000),(27,0x4000000),(28,0x8000100),(29,0x200),(31,0x40040000)],[0,16,1,17,8,24,9,25,4,20,5,21,12,28,13,29,2,18,3,19,10,26,11,27,6,22,7,23,14,30,15,31]),([(3,0xa),(4,0x50),(7,0xa0),(8,0x500),(11,0xa00),(12,0x5000),(15,0xa000),(17,0x50000),(20,0xa0000),(21,0x500000),(24,0xa00000),(25,0x5000000),(28,0xa000000),(29,0x50000000)],[0,16,2,18,1,17,3,19,4,20,6,22,5,21,7,23,8,24,10,26,9,25,11,27,12,28,14,30,13,29,15,31]),([(3,0xa0a),(12,0x5050),(15,0xa0a0),(17,0x5050000),(20,0xa0a0000),(29,0x50500000)],[0,16,2,18,1,17,3,19,8,24,10,26,9,25,11,27,4,20,6,22,5,21,7,23,12,28,14,30,13,29,15,31]),([(7,0xaa),(8,0x5500),(15,0xaa00),(17,0x550000),(24,0xaa0000),(25,0x55000000)],[0,16,2,18,4,20,6,22,1,17,3,19,5,21,7,23,8,24,10,26,12,28,14,30,9,25,11,27,13,29,15,31]),([(15,0xaaaa),(17,0x55550000)],[0,16,2,18,4,20,6,22,8,24,10,26,12,28,14,30,1,17,3,19,5,21,7,23,9,25,11,27,13,29,15,31]),([(3,0xa00),(4,0xa00000),(7,0xa),(8,0x5000),(12,0x50),(13,0x5000000),(15,0xa000),(17,0x50000),(19,0xa0),(20,0xa000000),(24,0xa0000),(25,0x50000000),(28,0x500),(29,0x500000)],[0,16,2,18,8,24,10,26,1,17,3,19,9,25,11,27,4,20,6,22,12,28,14,30,5,21,7,23,13,29,15,31]),([(4,0xa00050),(11,0xa00),(13,0x5000000),(15,0xa00a),(17,0x50050000),(19,0xa0),(21,0x500000),(28,0xa000500)],[0,16,2,18,8,24,10,26,4,20,6,22,12,28,14,30,1,17,3,19,9,25,11,27,5,21,7,23,13,29,15,31]),([(1,0x20),(2,0x8000000),(3,0x2),(4,0x40),(6,0x1004),(7,0x80),(8,0x100),(9,0x2008),(11,0x200),(12,0x4000),(14,0x400),(15,0x108000),(17,0x10800),(18,0x200000),(20,0x20000),(21,0x400000),(23,0x10040000),(24,0x800000),(25,0x1000000),(26,0x20080000),(28,0x2000000),(29,0x40000000),(30,0x10),(31,0x4000000)],[0,16,4,20,1,17,5,21,2,18,6,22,3,19,7,23,8,24,12,28,9,25,13,29,10,26,14,30,11,27,15,31]),([(1,0x2020),(2,0x8080000),(3,0x202),(12,0x4040),(14,0x404),(15,0x10108080),(17,0x1010808),(18,0x20200000),(20,0x2020000),(29,0x40400000),(30,0x1010),(31,0x4040000)],[0,16,4,20,1,17,5,21,8,24,12,28,9,25,13,29,2,18,6,22,3,19,7,23,10,26,14,30,11,27,15,31]),([(2,0x8000004),(5,0x20),(6,0x1000),(7,0x82),(8,0x4100),(9,0x8),(10,0x400),(13,0x2000),(15,0x108200),(17,0x410800),(19,0x40000),(22,0x200000),(23,0x10000000),(24,0x820000),(25,0x41000000),(26,0x80000),(27,0x4000000),(30,0x20000010)],[0,16,4,20,2,18,6,22,1,17,5,21,3,19,7,23,8,24,12,28,10,26,14,30,9,25,13,29,11,27,15,31]),([(2,0x8080404),(13,0x2020),(15,0x10108282),(17,0x41410808),(19,0x4040000),(30,0x20201010)],[0,16,4,20,2,18,6,22,8,24,12,28,10,26,14,30,1,17,5,21,3,19,7,23,9,25,13,29,11,27,15,31]),([(1,0x2000),(2,0x8000000),(3,0x200),(4,0x800000),(5,0x20),(6,0x80000),(7,0x2),(8,0x4000),(10,0x400),(11,0x10000000),(12,0x40),(13,0x1000000),(14,0x4),(15,0x108000),(17,0x10800),(18,0x20000000),(19,0x80),(20,0x2000000),(21,0x8),(22,0x200000),(24,0x20000),(25,0x40000000),(26,0x1000),(27,0x4000000),(28,0x100),(29,0x400000),(30,0x10),(31,0x40000)],[0,16,4,20,8,24,12,28,1,17,5,21,9,25,13,29,2,18,6,22,10,26,14,30,3,19,7,23,11,27,15,31]),([(2,0x8000400),(4,0x800040),(6,0x80004),(9,0x2000),(11,0x10000200),(13,0x1000020),(15,0x108002),(17,0x40010800),(19,0x4000080),(21,0x400008),(23,0x40000),(26,0x20001000),(28,0x2000100),(30,0x200010)],[0,16,4,20,8,24,12,28,2,18,6,22,10,26,14,30,1,17,5,21,9,25,13,29,3,19,7,23,11,27,15,31]),([(3,0x400802),(6,0x801004),(9,0x2008),(11,0x1000000),(12,0x4010),(14,0x2000000),(15,0x8020),(17,0x4010000),(18,0x40),(20,0x8020000),(21,0x80),(23,0x10040000),(26,0x20080100),(29,0x40100200)],[0,16,8,24,1,17,9,25,2,18,10,26,3,19,11,27,4,20,12,28,5,21,13,29,6,22,14,30,7,23,15,31]),([(1,0x2000),(2,0x80000),(3,0x400002),(4,0x10),(6,0x800000),(7,0x20),(8,0x400),(11,0x1000800),(12,0x4000),(14,0x2000004),(15,0x10008000),(17,0x10008),(18,0x20000040),(20,0x20000),(21,0x100080),(24,0x200000),(25,0x4000000),(26,0x100),(28,0x8000000),(29,0x40000200),(30,0x1000),(31,0x40000)],[0,16,8,24,1,17,9,25,4,20,12,28,5,21,13,29,2,18,10,26,3,19,11,27,6,22,14,30,7,23,15,31]),([(1,0x200),(2,0x4),(3,0x800),(4,0x200000),(6,0x801000),(7,0x2),(8,0x4000),(9,0x8),(11,0x1000000),(12,0x10),(13,0x4002000),(14,0x40),(15,0x8000),(17,0x10000),(18,0x2000000),(19,0x40020),(20,0x8000000),(21,0x80),(23,0x10000000),(24,0x20000),(25,0x40000000),(26,0x80100),(28,0x400),(29,0x100000),(30,0x20000000),(31,0x400000)],[0,16,8,24,2,18,10,26,1,17,9,25,3,19,11,27,4,20,12,28,6,22,14,30,5,21,13,29,7,23,15,31]),([(2,0x80004),(4,0x200010),(6,0x800040),(9,0x200),(11,0x1000800),(13,0x4002000),(15,0x10008002),(17,0x40010008),(19,0x40020),(21,0x100080),(23,0x400000),(26,0x2000100),(28,0x8000400),(30,0x20001000)],[0,16,8,24,2,18,10,26,4,20,12,28,6,22,14,30,1,17,9,25,3,19,11,27,5,21,13,29,7,23,15,31]),([(1,0x2200),(6,0x880000),(7,0x22),(8,0x4400),(11,0x11000000),(14,0x44),(15,0x8800),(17,0x110000),(18,0x22000000),(21,0x88),(24,0x220000),(25,0x44000000),(26,0x1100),(31,0x440000)],[0,16,8,24,4,20,12,28,1,17,9,25,5,21,13,29,2,18,10,26,6,22,14,30,3,19,11,27,7,23,15,31]),([(6,0x880044),(9,0x2200),(11,0x11000000),(15,0x8822),(17,0x44110000),(21,0x88),(23,0x440000),(26,0x22001100)],[0,16,8,24,4,20,12,28,2,18,10,26,6,22,14,30,1,17,9,25,5,21,13,29,3,19,11,27,7,23,15,31])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5maps_ok : validMaps x5maps 0xfee8e880 := by
  have h : x5maps.all (goodShift 0xfee8e880) = true := by decide +kernel
  exact fun p hp => goodShift_ok (Array.all_eq_true_iff_forall_mem.mp h p hp)
def x5s2d0 : Array (List Word) := #[[inputA,0xfcccf000,0xfff0ccc0]]
def x5s2d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d0g0 : ∀ q (hq : q < x5s2d0.size), 0 ≤ q → q < 1 → ¬ Reach x5s2d0[q].toFinset 2 0 0xfee8e880 := by
  have check : part x5s2d0 0xfee8e880 2 0 #[] #[] 0 x5s2d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d0ok : correct x5s2d0 2 0 0xfee8e880 := by
  exact fun q hq => x5s2d0g0 q hq (Nat.zero_le _) hq
def x5s2d0r : Array (List Word) := #[[inputA,0xfcccf000,0xfff0ccc0],[0xeee0eee0,0xf888f888,inputE]]
def x5s2d0rg0c : List (ℕ × ℕ) := [(0,0),(0,45)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d0rg0 : ∀ q (hq : q < x5s2d0r.size), 0 ≤ q → q < 2 → ¬ Reach x5s2d0r[q].toFinset 2 0 0xfee8e880 := by
  have check : aliasPart x5s2d0r x5s2d0 0xfee8e880 x5maps 0 x5s2d0rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s2d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d0rok : correct x5s2d0r 2 0 0xfee8e880 := by
  exact fun q hq => x5s2d0rg0 q hq (Nat.zero_le _) hq
def x5s2d1 : Array (List Word) := #[[inputA,0xfcccf000,0xfff0ccc0]]
def x5s2d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0],[0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d1g0 : ∀ q (hq : q < x5s2d1.size), 0 ≤ q → q < 1 → ¬ Reach x5s2d1[q].toFinset 2 1 0xfee8e880 := by
  have check : part x5s2d1 0xfee8e880 2 1 #[] x5s2d0r 0 x5s2d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x5s2d0rok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d1ok : correct x5s2d1 2 1 0xfee8e880 := by
  exact fun q hq => x5s2d1g0 q hq (Nat.zero_le _) hq
def x5s2d1r : Array (List Word) := #[[inputA,0xfcccf000,0xfff0ccc0],[0xeee0eee0,0xf888f888,inputE]]
def x5s2d1rg0c : List (ℕ × ℕ) := [(0,0),(0,45)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d1rg0 : ∀ q (hq : q < x5s2d1r.size), 0 ≤ q → q < 2 → ¬ Reach x5s2d1r[q].toFinset 2 1 0xfee8e880 := by
  have check : aliasPart x5s2d1r x5s2d1 0xfee8e880 x5maps 0 x5s2d1rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s2d1ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s2d1rok : correct x5s2d1r 2 1 0xfee8e880 := by
  exact fun q hq => x5s2d1rg0 q hq (Nat.zero_le _) hq
def x5s3d0 : Array (List Word) := #[[0x88888888,0xe0e0e0e0,0xfe00fe00,inputE],[0x88888888,0xeee0eee0,0xf000f000,inputE],[inputA,0xfccccccc,0xfff0f0f0,0xffffff00],[inputA,0xfcccf000,0xfff0fff0,0xffffcccc]]
def x5s3d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,1,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d0g0 : ∀ q (hq : q < x5s3d0.size), 0 ≤ q → q < 4 → ¬ Reach x5s3d0[q].toFinset 3 0 0xfee8e880 := by
  have check : part x5s3d0 0xfee8e880 3 0 x5s2d0r #[] 0 x5s3d0g0c = true := by decide +kernel
  exact part_ok x5s2d0rok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d0ok : correct x5s3d0 3 0 0xfee8e880 := by
  exact fun q hq => x5s3d0g0 q hq (Nat.zero_le _) hq
def x5s3d0r : Array (List Word) := #[[0x88888888,0xe0e0e0e0,0xfe00fe00,inputE],[0x88888888,0xe0e0e0e0,0xfefe0000,inputD],[0x88888888,0xee00ee00,0xf0e0f0e0,inputE],[0x88888888,0xeee0eee0,0xf000f000,inputE],[0xa8a8a8a8,0xc0c0c0c0,0xfe00fe00,inputE],[inputA,0xfccccccc,0xfff0f0f0,0xffffff00],[inputA,0xfcccf000,0xfff0fff0,0xffffcccc],[0xeaeaeaea,0xfcfcfcfc,inputD,0xffff8080],[0xeaeaeaea,0xfcfcfcfc,0xff80ff80,inputE],[0xeeeeeeee,inputC,0xff888888,0xffffff00],[0xeeeeeeee,inputC,0xff88ff00,0xffff8888],[0xeeeeeeee,0xf888f888,0xfff0fff0,inputE],[0xeeeeeeee,0xf8f8f8f8,inputD,0xffff8080]]
def x5s3d0rg0c : List (ℕ × ℕ) := [(0,0),(0,1),(0,2),(1,0),(0,48),(2,0),(3,0),(2,64),(2,65),(3,42),(2,90),(3,45),(2,94)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d0rg0 : ∀ q (hq : q < x5s3d0r.size), 0 ≤ q → q < 13 → ¬ Reach x5s3d0r[q].toFinset 3 0 0xfee8e880 := by
  have check : aliasPart x5s3d0r x5s3d0 0xfee8e880 x5maps 0 x5s3d0rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s3d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d0rok : correct x5s3d0r 3 0 0xfee8e880 := by
  exact fun q hq => x5s3d0rg0 q hq (Nat.zero_le _) hq
def x5s3d1 : Array (List Word) := #[[0x88888888,0xe0e0e0e0,0xfe00fe00,inputE],[0x88888888,0xeee0eee0,0xf000f000,inputE],[inputA,0xfccccccc,0xfff0f0f0,0xffffff00],[inputA,0xfcccf000,0xfff0fff0,0xffffcccc]]
def x5s3d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0]),([0,0,0,1,0,0,0,0,0,0,0,0],[3,3,3,3]),([0,0,0,0,0,0,0,0,0,0,0,0],[5,5,5,5]),([0,0,0,0,0,0,0,0,0,0,0,0],[6,6,6,6])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d1g0 : ∀ q (hq : q < x5s3d1.size), 0 ≤ q → q < 4 → ¬ Reach x5s3d1[q].toFinset 3 1 0xfee8e880 := by
  have check : part x5s3d1 0xfee8e880 3 1 x5s2d1r x5s3d0r 0 x5s3d1g0c = true := by decide +kernel
  exact part_ok x5s2d1rok x5s3d0rok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d1ok : correct x5s3d1 3 1 0xfee8e880 := by
  exact fun q hq => x5s3d1g0 q hq (Nat.zero_le _) hq
def x5s3d1r : Array (List Word) := #[[0x88888888,0xe0e0e0e0,0xfe00fe00,inputE],[0x88888888,0xe0e0e0e0,0xfefe0000,inputD],[0x88888888,0xee00ee00,0xf0e0f0e0,inputE],[0x88888888,0xeee0eee0,0xf000f000,inputE],[0xa8a8a8a8,0xc0c0c0c0,0xfe00fe00,inputE],[0xeaeaeaea,0xfcfcfcfc,inputD,0xffff8080],[0xeaeaeaea,0xfcfcfcfc,0xff80ff80,inputE],[0xeeeeeeee,inputC,0xff888888,0xffffff00],[0xeeeeeeee,inputC,0xff88ff00,0xffff8888],[0xeeeeeeee,0xf888f888,0xfff0fff0,inputE],[0xeeeeeeee,0xf8f8f8f8,inputD,0xffff8080]]
def x5s3d1rg0c : List (ℕ × ℕ) := [(0,0),(0,1),(0,2),(1,0),(0,48),(2,64),(2,65),(3,42),(2,90),(3,45),(2,94)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d1rg0 : ∀ q (hq : q < x5s3d1r.size), 0 ≤ q → q < 11 → ¬ Reach x5s3d1r[q].toFinset 3 1 0xfee8e880 := by
  have check : aliasPart x5s3d1r x5s3d1 0xfee8e880 x5maps 0 x5s3d1rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s3d1ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s3d1rok : correct x5s3d1r 3 1 0xfee8e880 := by
  exact fun q hq => x5s3d1rg0 q hq (Nat.zero_le _) hq
def x5s4d0 : Array (List Word) := #[[0x888888,0xeeeeeeee,inputC,inputD,inputE],[0xaaaaaa,inputB,0xfaf0f0f0,inputD,inputE],[0xffff00,inputA,inputB,inputC,0xff000000],[0x2aaaaaa,inputB,inputC,inputD,inputE],[0xaaaaaaa,0xccccccc,inputC,inputD,inputE],[0xaaaaaaa,inputB,0xf000f000,0xfff0fff0,inputE],[0xaaaaaaa,inputB,inputC,inputD,inputE],[0xaaaaaaa,inputC,0xfccccccc,inputD,inputE],[0xff0fff0,inputA,inputB,0xf000f000,inputE],[0x2aaaaaaa,inputB,inputC,inputD,inputE],[0x80808080,0xeaeaeaea,0xfcfcfcfc,inputD,inputE],[0x88888888,0xe0e0e0e0,0xfefefefe,inputD,inputE],[0x88888888,0xe6e6e6e6,inputC,inputD,inputE],[0x88888888,0xeee0eee0,inputC,inputD,inputE],[0x88888888,0xeeeaeeea,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf000f000,0xfff0fff0,inputE],[0x88888888,0xeeeeeeee,0xf0e0f0e0,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffff0011],[0x88888888,0xeeeeeeee,inputC,inputD,0xffff8080],[0x88888888,0xeeeeeeff,inputC,inputD,inputE],[0x88889999,0xeeeeeeee,inputC,inputD,inputE],[0x8888aaaa,0xeeeecccc,inputC,inputD,inputE],[0x8aaaaaaa,inputB,inputC,inputD,inputE],[0x98989898,0xeeeeeeee,inputC,inputD,inputE],[0x99999999,0xeeeeeeee,inputC,inputD,inputE],[0xa888a888,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfe00fe00,inputE],[0xa8a8a8a8,inputB,0xf2f2f2f2,inputD,inputE],[0xa8a8a8a8,inputB,0xfaf0faf0,inputD,inputE],[0xaaa8a8a8,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xfffc0000],[0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xffff0003],[0xaaa8aaa8,inputB,inputC,0xff03ff03,inputE],[0xaaa8aaaa,inputB,inputC,inputD,inputE],[0xaaaaaaa8,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff0001],[inputA,inputB,inputC,inputD,0xffff0002],[inputA,inputB,inputC,inputD,0xffff0003],[inputA,inputB,inputC,inputD,0xffff0007],[inputA,inputB,inputC,inputD,0xffff0080],[inputA,inputB,inputC,inputD,0xffff8000],[inputA,inputB,inputC,inputD,0xffff8080],[inputA,inputB,inputC,inputD,0xffff8880],[inputA,inputB,inputC,0xff01ff01,0xffff0101],[inputA,inputB,inputC,0xff80ff80,0xffff8080],[inputA,inputB,inputC,0xff888888,0xffffff00],[inputA,inputB,inputC,0xff88ff00,0xffff8888]]
def x5s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g0 : ∀ q (hq : q < x5s4d0.size), 0 ≤ q → q < 4 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 0 x5s4d0g0c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g4 : ∀ q (hq : q < x5s4d0.size), 4 ≤ q → q < 8 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 4 x5s4d0g4c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,8,0,7,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g8 : ∀ q (hq : q < x5s4d0.size), 8 ≤ q → q < 12 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 8 x5s4d0g8c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g12c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,11,0,0,0,0,0,0,3,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g12 : ∀ q (hq : q < x5s4d0.size), 12 ≤ q → q < 16 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 12 x5s4d0g12c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g16c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g16 : ∀ q (hq : q < x5s4d0.size), 16 ≤ q → q < 20 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 16 x5s4d0g16c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g20c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g20 : ∀ q (hq : q < x5s4d0.size), 20 ≤ q → q < 24 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 20 x5s4d0g20c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g24c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g24 : ∀ q (hq : q < x5s4d0.size), 24 ≤ q → q < 28 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 24 x5s4d0g24c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g28c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g28 : ∀ q (hq : q < x5s4d0.size), 28 ≤ q → q < 32 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 28 x5s4d0g28c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g32c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g32 : ∀ q (hq : q < x5s4d0.size), 32 ≤ q → q < 36 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 32 x5s4d0g32c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g36c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g36 : ∀ q (hq : q < x5s4d0.size), 36 ≤ q → q < 40 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 36 x5s4d0g36c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g40c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g40 : ∀ q (hq : q < x5s4d0.size), 40 ≤ q → q < 44 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 40 x5s4d0g40c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g44c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g44 : ∀ q (hq : q < x5s4d0.size), 44 ≤ q → q < 48 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 44 x5s4d0g44c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
def x5s4d0g48c : List (List ℕ × List ℕ) := [([0,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0g48 : ∀ q (hq : q < x5s4d0.size), 48 ≤ q → q < 50 → ¬ Reach x5s4d0[q].toFinset 4 0 0xfee8e880 := by
  have check : part x5s4d0 0xfee8e880 4 0 x5s3d0r #[] 48 x5s4d0g48c = true := by decide +kernel
  exact part_ok x5s3d0rok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0ok : correct x5s4d0 4 0 0xfee8e880 := by
  intro q hq
  have lim : q < 50 := hq
  by_cases atMid : q < 24
  ·
    by_cases atMid : q < 12
    ·
      by_cases atMid : q < 4
      ·
        exact x5s4d0g0 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 8
        ·
          exact x5s4d0g4 q hq (by omega) (by omega)
        ·
          exact x5s4d0g8 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 16
      ·
        exact x5s4d0g12 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 20
        ·
          exact x5s4d0g16 q hq (by omega) (by omega)
        ·
          exact x5s4d0g20 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 36
    ·
      by_cases atMid : q < 28
      ·
        exact x5s4d0g24 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 32
        ·
          exact x5s4d0g28 q hq (by omega) (by omega)
        ·
          exact x5s4d0g32 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 44
      ·
        by_cases atMid : q < 40
        ·
          exact x5s4d0g36 q hq (by omega) (by omega)
        ·
          exact x5s4d0g40 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 48
        ·
          exact x5s4d0g44 q hq (by omega) (by omega)
        ·
          exact x5s4d0g48 q hq (by omega) (by omega)
def x5s4d0r : Array (List Word) := #[[0x888888,0xeeeeeeee,inputC,inputD,inputE],[0xaaaaaa,inputB,0xfaf0f0f0,inputD,inputE],[0xaaaaaa,0xeecccccc,inputC,inputD,inputE],[0xf0f0f0,inputA,0xfccccccc,inputD,inputE],[0xffff00,inputA,inputB,inputC,0xff000000],[0x2aaaaaa,inputB,inputC,inputD,inputE],[0xaaaaaaa,0xccccccc,inputC,inputD,inputE],[0xaaaaaaa,inputB,0xf000f000,0xfff0fff0,inputE],[0xaaaaaaa,inputB,inputC,inputD,inputE],[0xaaaaaaa,inputC,0xfccccccc,inputD,inputE],[0xccccccc,inputA,0xf000f000,0xfff0fff0,inputE],[0xccccccc,inputA,inputC,inputD,inputE],[0xf00ff00,inputA,inputC,0xfccccccc,inputE],[0xff0fff0,inputA,inputB,0xf000f000,inputE],[0xfff0000,inputA,inputC,0xfccccccc,inputD],[0x2aaaaaaa,inputB,inputC,inputD,inputE],[0x30f0f0f0,inputA,inputB,inputD,inputE],[0x3f00ff00,inputA,inputB,inputC,inputE],[0x3fff0000,inputA,inputB,inputC,inputD],[0x5555aaaa,0xaaaa0000,inputB,inputC,inputD],[0x80808080,0xeaeaeaea,0xfcfcfcfc,inputD,inputE],[0x80808080,0xeeeeeeee,0xf8f8f8f8,inputD,inputE],[0x88888888,0xe0e0e0e0,0xfefefefe,inputD,inputE],[0x88888888,0xe6e6e6e6,inputC,inputD,inputE],[0x88888888,0xeee0eee0,inputC,inputD,inputE],[0x88888888,0xeeeaeeea,inputC,inputD,inputE],[0x88888888,0xeeeceeec,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf000f000,0xfff0fff0,inputE],[0x88888888,0xeeeeeeee,0xf0e0f0e0,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfe00fe00,inputE],[0x88888888,0xeeeeeeee,inputC,0xfefe0000,inputD],[0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffff0011],[0x88888888,0xeeeeeeee,inputC,inputD,0xffff8080],[0x88888888,0xeeeeeeee,inputC,0xff80ff80,inputE],[0x88888888,0xeeeeeeff,inputC,inputD,inputE],[0x8ccccccc,inputA,inputC,inputD,inputE],[0x99999999,0xeeeeeeee,inputC,inputD,inputE],[0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0xa2a2a2a2,inputB,0xf8f8f8f8,inputD,inputE],[0xa888a888,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,0xc0c0c0c0,0xfefefefe,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfe00fe00,inputE],[0xa8a8a8a8,inputB,inputC,0xfefe0000,inputD],[0xa8a8a8a8,inputB,0xfaf0faf0,inputD,inputE],[0xaa00aa00,inputB,inputC,0xffaaffaa,inputE],[0xaaa0aaa0,inputB,inputC,0xff88ff88,inputE],[0xaaa0aaa0,inputB,0xf8f8f8f8,inputD,inputE],[0xaaa8a8a8,inputB,inputC,inputD,inputE],[0xaaa8aaa8,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[0xaaa8aaa8,inputB,inputC,0xfc00fc00,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xfffc0000],[0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xaaaa00aa,inputB,inputC,inputD,0xffffaa00],[0xaaaa8888,0xcccceeee,inputC,inputD,inputE],[0xaaaaa0a0,inputB,inputC,inputD,0xffff8888],[0xaaaaa8a8,inputB,inputC,inputD,inputE],[0xaaaaaa00,inputB,inputC,inputD,0xffff00aa],[0xaaaaaa00,inputB,inputC,0xff00ffaa,inputE],[0xaaaaaa88,inputB,inputC,inputD,inputE],[0xaaaaaa88,0xccccccff,inputC,inputD,inputE],[0xaaaaaaa0,inputB,inputC,inputD,inputE],[0xaaaaaaa0,inputB,inputC,inputD,0xffff000f],[0xaaaaaaa0,inputB,inputC,0xff00ff0f,inputE],[0xaaaaaaa0,inputB,0xf0f0f0ff,inputD,inputE],[0xaaaaaaa0,0xcccccccf,inputC,inputD,inputE],[0xaaaaaaa8,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[inputA,0xccc8ccc8,inputC,inputD,inputE],[inputA,0xcccc0000,inputC,inputD,0xffffcccc],[inputA,0xccccc0c0,inputC,inputD,0xffff8888],[inputA,0xccccccc0,inputC,inputD,0xffff000f],[inputA,inputB,0xeee0eee0,0xf000f000,inputE],[inputA,inputB,0xf000f000,0xfff0fff0,inputE],[inputA,inputB,0xf000f00f,0xfff0fff0,inputE],[inputA,inputB,0xf0e0f0e0,inputD,inputE],[inputA,inputB,0xf0f00000,inputD,0xfffff0f0],[inputA,inputB,0xf0f000f0,inputD,0xfffff000],[inputA,inputB,0xf0f08080,inputD,0xfffff0f0],[inputA,inputB,inputC,0xfe00fe00,inputE],[inputA,inputB,inputC,0xfe00fe00,0xffff0101],[inputA,inputB,inputC,0xfe00ff00,inputE],[inputA,inputB,inputC,0xfeee0000,inputD],[inputA,inputB,inputC,0xfefe0000,inputD],[inputA,inputB,inputC,0xff000000,0xffffff00],[inputA,inputB,inputC,0xff0000aa,0xffffff00],[inputA,inputB,inputC,0xff0000ff,0xffffff00],[inputA,inputB,inputC,0xff000f00,0xfffff000],[inputA,inputB,inputC,inputD,0xfffc0000],[inputA,inputB,inputC,inputD,0xfffe0000],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff0003],[inputA,inputB,inputC,inputD,0xffff0011],[inputA,inputB,inputC,inputD,0xffff0101],[inputA,inputB,inputC,inputD,0xffff8000],[inputA,inputB,inputC,inputD,0xffff8080],[inputA,inputB,inputC,inputD,0xffff8880],[inputA,inputB,inputC,inputD,0xffffc000],[inputA,inputB,inputC,0xff00ff03,inputE],[inputA,inputB,inputC,0xff00ff80,inputE],[inputA,inputB,inputC,0xff80ff80,inputE],[inputA,inputB,inputC,0xff80ff80,0xffff8080],[inputA,inputB,inputC,0xff888888,0xffffff00],[inputA,inputB,inputC,0xff88ff00,inputE],[inputA,inputB,inputC,0xff88ff00,0xffff8888],[inputA,inputB,0xf0f0f0f3,inputD,inputE],[inputA,inputB,0xf888f888,0xfff0fff0,inputE],[inputA,inputB,0xf8f0f8f0,inputD,inputE],[inputA,inputB,0xf8f8f8f8,inputD,0xffff8080],[inputA,inputB,0xf8f8f8f8,0xff80ff80,inputE],[inputA,inputB,0xfaf0f0f0,inputD,inputE],[inputA,0xccccccce,inputC,inputD,inputE],[inputA,0xcccccccf,0xf000f000,0xfff0fff0,inputE],[inputA,0xcccccccf,inputC,inputD,inputE],[inputA,0xeac0eac0,0xfcfcfcfc,inputD,inputE],[inputA,0xeccceccc,inputC,inputD,inputE],[inputA,inputC,0xfccccccc,inputD,inputE],[0xaaaaaaab,inputB,inputC,inputD,inputE],[0xaaaaaaaf,inputB,0xf000f000,0xfff0fff0,inputE],[0xaaaaaaaf,inputB,inputC,inputD,inputE],[0xaaaaaaaf,0xcccccccf,inputC,inputD,inputE],[0xaaaaaabf,inputB,inputC,inputD,inputE],[inputB,0xeaaaeaaa,inputC,inputD,inputE],[inputB,0xeac0eac0,inputC,0xffaaffaa,inputE],[inputB,inputC,0xfaaaaaaa,inputD,inputE]]
def x5s4d0rg0c : List (ℕ × ℕ) := [(0,0),(1,0),(1,6),(1,30),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(5,24),(6,24),(1,32),(8,0),(1,33),(9,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg0 : ∀ q (hq : q < x5s4d0r.size), 0 ≤ q → q < 16 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 0 x5s4d0rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
def x5s4d0rg16c : List (ℕ × ℕ) := [(6,30),(6,32),(6,33),(2,72),(10,0),(10,30),(11,0),(12,0),(13,0),(14,0),(14,24),(15,0),(16,0),(16,2),(16,3),(17,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg16 : ∀ q (hq : q < x5s4d0r.size), 16 ≤ q → q < 32 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 16 x5s4d0rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
def x5s4d0rg32c : List (ℕ × ℕ) := [(18,0),(19,0),(19,1),(20,0),(23,24),(25,0),(17,6),(22,18),(26,0),(11,48),(27,0),(27,1),(29,0),(17,8),(29,12),(29,14)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg32 : ∀ q (hq : q < x5s4d0r.size), 32 ≤ q → q < 48 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 32 x5s4d0rg32c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
def x5s4d0rg48c : List (ℕ × ℕ) := [(30,0),(16,48),(27,80),(31,0),(32,0),(17,9),(22,9),(28,9),(29,13),(32,1),(28,16),(28,17),(32,4),(34,16),(32,18),(34,18)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg48 : ∀ q (hq : q < x5s4d0r.size), 48 ≤ q → q < 64 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 48 x5s4d0rg48c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
def x5s4d0rg64c : List (ℕ × ℕ) := [(34,19),(34,22),(33,18),(36,0),(17,48),(32,24),(17,51),(29,73),(34,96),(13,60),(17,60),(21,60),(32,30),(17,61),(22,61),(26,61)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg64 : ∀ q (hq : q < x5s4d0r.size), 64 ≤ q → q < 80 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 64 x5s4d0rg64c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
def x5s4d0rg80c : List (ℕ × ℕ) := [(32,32),(33,32),(35,32),(30,33),(32,33),(17,64),(24,64),(25,64),(22,64),(32,105),(36,33),(37,0),(40,0),(40,30),(40,32),(43,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg80 : ∀ q (hq : q < x5s4d0r.size), 80 ≤ q → q < 96 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 80 x5s4d0rg80c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
def x5s4d0rg96c : List (ℕ × ℕ) := [(44,0),(45,0),(44,72),(40,1),(42,1),(44,1),(47,0),(48,0),(44,3),(49,0),(40,4),(48,3),(44,4),(49,4),(49,5),(44,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg96 : ∀ q (hq : q < x5s4d0r.size), 96 ≤ q → q < 112 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 96 x5s4d0rg96c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
def x5s4d0rg112c : List (ℕ × ℕ) := [(39,18),(18,66),(40,18),(48,16),(44,18),(44,90),(38,96),(18,108),(40,96),(46,90),(41,96),(44,96),(48,73),(44,114)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rg112 : ∀ q (hq : q < x5s4d0r.size), 112 ≤ q → q < 126 → ¬ Reach x5s4d0r[q].toFinset 4 0 0xfee8e880 := by
  have check : aliasPart x5s4d0r x5s4d0 0xfee8e880 x5maps 112 x5s4d0rg112c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d0rok : correct x5s4d0r 4 0 0xfee8e880 := by
  intro q hq
  have lim : q < 126 := hq
  by_cases atMid : q < 64
  ·
    by_cases atMid : q < 32
    ·
      by_cases atMid : q < 16
      ·
        exact x5s4d0rg0 q hq (by omega) (by omega)
      ·
        exact x5s4d0rg16 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 48
      ·
        exact x5s4d0rg32 q hq (by omega) (by omega)
      ·
        exact x5s4d0rg48 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 96
    ·
      by_cases atMid : q < 80
      ·
        exact x5s4d0rg64 q hq (by omega) (by omega)
      ·
        exact x5s4d0rg80 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 112
      ·
        exact x5s4d0rg96 q hq (by omega) (by omega)
      ·
        exact x5s4d0rg112 q hq (by omega) (by omega)
def x5s4d1 : Array (List Word) := #[[0x80808080,0xeaeaeaea,0xfcfcfcfc,inputD,inputE],[0x88888888,0xe0e0e0e0,0xfefefefe,inputD,inputE],[0x88888888,0xeee0eee0,inputC,inputD,inputE],[0x88888888,0xeeeaeeea,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf000f000,0xfff0fff0,inputE],[0x88888888,0xeeeeeeee,0xf0e0f0e0,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffff8080],[0xa888a888,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfe00fe00,inputE],[0xa8a8a8a8,inputB,0xfaf0faf0,inputD,inputE],[0xaaa8a8a8,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xfffc0000],[0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xaaaaaaa8,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff8000],[inputA,inputB,inputC,inputD,0xffff8080],[inputA,inputB,inputC,inputD,0xffff8880],[inputA,inputB,inputC,0xff80ff80,0xffff8080],[inputA,inputB,inputC,0xff888888,0xffffff00],[inputA,inputB,inputC,0xff88ff00,0xffff8888]]
def x5s4d1g0c : List (List ℕ × List ℕ) := [([0,6,0,5,0,0,0,0,0,0,0,0,0,0,0,0],[20,20,20,20,20]),([0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],[22,22,22,22,22]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0],[24,24,24,24,24]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[25,25,25,25,25])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1g0 : ∀ q (hq : q < x5s4d1.size), 0 ≤ q → q < 4 → ¬ Reach x5s4d1[q].toFinset 4 1 0xfee8e880 := by
  have check : part x5s4d1 0xfee8e880 4 1 x5s3d1r x5s4d0r 0 x5s4d1g0c = true := by decide +kernel
  exact part_ok x5s3d1rok x5s4d0rok check
def x5s4d1g4c : List (List ℕ × List ℕ) := [([0,9,0,0,0,0,0,0,3,0,0,0,0,0,0,0],[27,27,27,27,27]),([0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0],[28,28,28,28,28]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[31,31,31,31,31]),([0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x21,0x21,0x21,0x21,0x21])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1g4 : ∀ q (hq : q < x5s4d1.size), 4 ≤ q → q < 8 → ¬ Reach x5s4d1[q].toFinset 4 1 0xfee8e880 := by
  have check : part x5s4d1 0xfee8e880 4 1 x5s3d1r x5s4d0r 4 x5s4d1g4c = true := by decide +kernel
  exact part_ok x5s3d1rok x5s4d0rok check
def x5s4d1g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x28,0x28,0x28,0x28,0x28]),([0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0],[0x2a,0x2a,0x2a,0x2a,0x2a]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x2c,0x2c,0x2c,0x2c,0x2c]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x30,0x30,0x30,0x30,0x30])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1g8 : ∀ q (hq : q < x5s4d1.size), 8 ≤ q → q < 12 → ¬ Reach x5s4d1[q].toFinset 4 1 0xfee8e880 := by
  have check : part x5s4d1 0xfee8e880 4 1 x5s3d1r x5s4d0r 8 x5s4d1g8c = true := by decide +kernel
  exact part_ok x5s3d1rok x5s4d0rok check
def x5s4d1g12c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x33,0x33,0x33,0x33,0x33]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x34,0x34,0x34,0x34,0x34]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x43,0x43,0x43,0x43,0x43]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x5b,0x5b,0x5b,0x5b,0x5b])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1g12 : ∀ q (hq : q < x5s4d1.size), 12 ≤ q → q < 16 → ¬ Reach x5s4d1[q].toFinset 4 1 0xfee8e880 := by
  have check : part x5s4d1 0xfee8e880 4 1 x5s3d1r x5s4d0r 12 x5s4d1g12c = true := by decide +kernel
  exact part_ok x5s3d1rok x5s4d0rok check
def x5s4d1g16c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x5f,0x5f,0x5f,0x5f,0x5f]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x60,0x60,0x60,0x60,0x60]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x61,0x61,0x61,0x61,0x61]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x66,0x66,0x66,0x66,0x66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1g16 : ∀ q (hq : q < x5s4d1.size), 16 ≤ q → q < 20 → ¬ Reach x5s4d1[q].toFinset 4 1 0xfee8e880 := by
  have check : part x5s4d1 0xfee8e880 4 1 x5s3d1r x5s4d0r 16 x5s4d1g16c = true := by decide +kernel
  exact part_ok x5s3d1rok x5s4d0rok check
def x5s4d1g20c : List (List ℕ × List ℕ) := [([0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x67,0x67,0x67,0x67,0x67]),([0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x69,0x69,0x69,0x69,0x69])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1g20 : ∀ q (hq : q < x5s4d1.size), 20 ≤ q → q < 22 → ¬ Reach x5s4d1[q].toFinset 4 1 0xfee8e880 := by
  have check : part x5s4d1 0xfee8e880 4 1 x5s3d1r x5s4d0r 20 x5s4d1g20c = true := by decide +kernel
  exact part_ok x5s3d1rok x5s4d0rok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1ok : correct x5s4d1 4 1 0xfee8e880 := by
  intro q hq
  have lim : q < 22 := hq
  by_cases atMid : q < 12
  ·
    by_cases atMid : q < 4
    ·
      exact x5s4d1g0 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 8
      ·
        exact x5s4d1g4 q hq (by omega) (by omega)
      ·
        exact x5s4d1g8 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 16
    ·
      exact x5s4d1g12 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 20
      ·
        exact x5s4d1g16 q hq (by omega) (by omega)
      ·
        exact x5s4d1g20 q hq (by omega) (by omega)
def x5s4d1r : Array (List Word) := #[[0x80808080,0xeeeeeeee,0xf8f8f8f8,inputD,inputE],[0x88888888,0xe0e0e0e0,0xfefefefe,inputD,inputE],[0x88888888,0xeee0eee0,inputC,inputD,inputE],[0x88888888,0xeeeaeeea,inputC,inputD,inputE],[0x88888888,0xeeeceeec,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf000f000,0xfff0fff0,inputE],[0x88888888,0xeeeeeeee,inputC,0xfe00fe00,inputE],[0x88888888,0xeeeeeeee,inputC,0xfefe0000,inputD],[0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffff8080],[0x88888888,0xeeeeeeee,inputC,0xff80ff80,inputE],[0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0xa888a888,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,0xc0c0c0c0,0xfefefefe,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfe00fe00,inputE],[0xa8a8a8a8,inputB,inputC,0xfefe0000,inputD],[0xaaa0aaa0,inputB,inputC,0xff88ff88,inputE],[0xaaa0aaa0,inputB,0xf8f8f8f8,inputD,inputE],[0xaaa8aaa8,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[0xaaa8aaa8,inputB,inputC,0xfc00fc00,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xfffc0000],[0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xaaaaa0a0,inputB,inputC,inputD,0xffff8888],[inputA,0xccc8ccc8,inputC,inputD,inputE],[inputA,0xccccc0c0,inputC,inputD,0xffff8888],[inputA,inputB,0xeee0eee0,0xf000f000,inputE],[inputA,inputB,0xf000f000,0xfff0fff0,inputE],[inputA,inputB,0xf0e0f0e0,inputD,inputE],[inputA,inputB,0xf0f08080,inputD,0xfffff0f0],[inputA,inputB,inputC,0xfe00fe00,inputE],[inputA,inputB,inputC,0xfeee0000,inputD],[inputA,inputB,inputC,0xfefe0000,inputD],[inputA,inputB,inputC,inputD,0xfffe0000],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff8000],[inputA,inputB,inputC,inputD,0xffff8080],[inputA,inputB,inputC,inputD,0xffff8880],[inputA,inputB,inputC,0xff80ff80,inputE],[inputA,inputB,inputC,0xff80ff80,0xffff8080],[inputA,inputB,0xf888f888,0xfff0fff0,inputE],[inputA,inputB,0xf8f0f8f0,inputD,inputE],[inputA,inputB,0xf8f8f8f8,inputD,0xffff8080],[inputA,inputB,0xf8f8f8f8,0xff80ff80,inputE],[inputA,0xeac0eac0,0xfcfcfcfc,inputD,inputE],[inputA,0xeccceccc,inputC,inputD,inputE],[inputB,0xeaaaeaaa,inputC,inputD,inputE],[inputB,0xeac0eac0,inputC,0xffaaffaa,inputE]]
def x5s4d1rg0c : List (ℕ × ℕ) := [(0,30),(1,0),(2,0),(3,0),(3,24),(4,0),(5,2),(5,3),(6,0),(7,0),(7,1),(6,6),(8,0),(1,48),(9,0),(9,1)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1rg0 : ∀ q (hq : q < x5s4d1r.size), 0 ≤ q → q < 16 → ¬ Reach x5s4d1r[q].toFinset 4 1 0xfee8e880 := by
  have check : aliasPart x5s4d1r x5s4d1 0xfee8e880 x5maps 0 x5s4d1rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d1ok check
def x5s4d1rg16c : List (ℕ × ℕ) := [(10,12),(10,14),(5,48),(9,80),(12,0),(13,0),(10,13),(13,24),(10,73),(2,60),(6,60),(13,30),(8,61),(13,32),(11,33),(13,33)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1rg16 : ∀ q (hq : q < x5s4d1r.size), 16 ≤ q → q < 32 → ¬ Reach x5s4d1r[q].toFinset 4 1 0xfee8e880 := by
  have check : aliasPart x5s4d1r x5s4d1 0xfee8e880 x5maps 16 x5s4d1rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d1ok check
def x5s4d1rg32c : List (ℕ × ℕ) := [(14,33),(15,0),(16,0),(17,0),(18,0),(17,1),(19,0),(20,3),(17,4),(21,4),(21,5),(20,16),(17,18),(17,96),(20,73)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1rg32 : ∀ q (hq : q < x5s4d1r.size), 32 ≤ q → q < 47 → ¬ Reach x5s4d1r[q].toFinset 4 1 0xfee8e880 := by
  have check : aliasPart x5s4d1r x5s4d1 0xfee8e880 x5maps 32 x5s4d1rg32c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s4d1ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s4d1rok : correct x5s4d1r 4 1 0xfee8e880 := by
  intro q hq
  have lim : q < 47 := hq
  by_cases atMid : q < 16
  ·
    exact x5s4d1rg0 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 32
    ·
      exact x5s4d1rg16 q hq (by omega) (by omega)
    ·
      exact x5s4d1rg32 q hq (by omega) (by omega)
def x5s5d0 : Array (List Word) := #[[3,inputA,inputB,inputC,inputD,inputE],[10,inputA,inputB,inputC,inputD,inputE],[15,0xaaaaaaa0,inputB,inputC,inputD,inputE],[15,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[15,inputA,inputB,inputC,inputD,inputE],[15,inputA,0xcccccccf,inputC,inputD,inputE],[0x3f,inputA,inputB,inputC,inputD,inputE],[0x88,inputA,inputB,inputC,inputD,inputE],[0xaa,0xaaaaaa00,inputB,inputC,inputD,inputE],[0xaa,inputA,inputB,inputC,0xff000000,0xffffff00],[0xaa,inputA,inputB,inputC,inputD,inputE],[0xaa,0xaaaaaaff,inputB,inputC,inputD,inputE],[0xee,inputA,inputB,inputC,inputD,inputE],[0xff,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xff,0xaa00aa00,inputB,inputC,0xffaaffaa,inputE],[0xff,0xaaaaaa88,inputB,inputC,inputD,inputE],[0xff,inputA,inputB,inputC,0xff000000,0xffffff00],[0xff,inputA,inputB,inputC,0xff0000ff,0xffffff00],[0xff,inputA,inputB,inputC,inputD,inputE],[0x3ff,inputA,inputB,inputC,inputD,inputE],[0xaaa,inputA,inputB,inputC,inputD,inputE],[0xfff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfff,inputA,inputB,inputC,inputD,inputE],[0x3fff,inputA,inputB,inputC,inputD,inputE],[0x3fff,inputA,inputB,inputC,inputD,0xffffc000],[0x8080,inputA,inputB,inputC,inputD,inputE],[0x8888,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x8888,inputA,inputB,inputC,inputD,inputE],[0x8888,inputA,0xcccceeee,inputC,inputD,inputE],[0xa8a8,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0x55550000,0xaaaa0000,inputB,inputC,inputD],[0xaaaa,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xaaaa,0xaaaa0000,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xaaaa,0xaaaa8888,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[0xaaaa,inputA,0xcccc0000,inputC,inputD,0xffffcccc],[0xaaaa,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaaeeee,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa,inputB,0xeaeaeaea,inputC,inputD,inputE],[0xeaea,inputA,inputB,inputC,inputD,inputE],[0xeeee,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xeeee,inputA,inputB,inputC,inputD,inputE],[0xfefe,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xffff,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xffff,0xaaaaa8a8,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfefe0000,inputD],[0xffff,inputA,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffff8080],[0xffff,inputA,inputB,inputC,0xff80ff80,inputE],[0xffff,inputA,inputB,inputC,0xff88ff00,inputE],[0x3ffff,inputA,inputB,inputC,inputD,0xfffc0000],[0x3ffff,inputA,inputB,inputC,inputD,inputE],[0xaaaaa,inputA,inputB,inputC,inputD,inputE],[0xf333f,inputA,inputB,inputC,inputD,inputE],[0xfffff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfffff,inputA,inputB,inputC,inputD,inputE],[0x3f3f3f,inputA,inputB,inputC,inputD,inputE],[0x3fffff,inputA,inputB,inputC,inputD,inputE],[0x888888,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa,0xaa000000,inputB,inputC,inputD,inputE],[0xaaaaaa,0xaa00aa00,inputB,inputC,inputD,inputE],[0xaaaaaa,inputA,inputB,inputC,0xff000000,0xffffff00],[0xaaaaaa,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa,0xaaffffff,inputB,inputC,inputD,inputE],[0xaaaaaa,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaaffaa,inputA,inputB,inputC,inputD,inputE],[0xeeeeee,inputA,inputB,inputC,inputD,inputE],[0xffff00,0xffffff,inputA,inputB,inputC,0xff000000],[0xffff00,inputA,inputB,inputC,0xff000000,inputD],[0xffff00,inputA,inputB,inputC,0xff000000,0xffffff00],[0xffff00,inputA,inputB,inputC,inputD,inputE],[0xffffff,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xffffff,0xaa00aa00,inputB,inputC,0xffaaffaa,inputE],[0xffffff,inputA,inputB,inputC,0xff000000,0xffffff00],[0xffffff,inputA,inputB,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xfaf0f0f0,inputD,inputE],[0x3ffffff,inputA,inputB,inputC,inputD,inputE],[0xaaaaaaa,0xfffffff,inputB,inputC,inputD,inputE],[0xaaaaaaa,inputA,inputB,inputC,inputD,inputE],[0xaaaaaaa,inputB,0xf0000000,inputC,inputD,inputE],[0xaaaaaaa,inputB,0xf000f000,inputC,inputD,inputE],[0xfffffff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfffffff,inputA,inputB,inputC,inputD,inputE],[0xfffffff,inputA,inputC,0xfccccccc,inputD,inputE],[0x3fffffff,inputA,inputB,inputC,inputD,inputE],[0x80008000,inputA,inputB,inputC,inputD,inputE],[0x80808080,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,0xffff8080],[0x80808080,inputA,inputB,0xf8f8f8f8,inputD,inputE],[0x80808888,inputA,inputB,inputC,inputD,inputE],[0x8080aaaa,inputA,inputB,inputC,inputD,inputE],[0x8080ffff,inputA,inputB,inputC,inputD,inputE],[0x88808880,inputA,inputB,inputC,inputD,inputE],[0x88888888,0x8888ffff,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0x99999999,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x88888888,0xa2a2a2a2,inputB,inputC,inputD,inputE],[0x88888888,0xaaa0aaa0,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffff8080],[0x88888888,inputA,0xccccccff,inputC,inputD,inputE],[0x88888888,inputA,0xcccceeee,inputC,inputD,inputE],[0x88888888,inputA,0xecececec,inputC,inputD,inputE],[0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xaaaaffff,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xbbbbbbbb,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xe0e0e0e0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xeeeeffff,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf0f0ffff,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf1f1f1f1,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf3f3f3f3,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf7f7f7f7,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE],[0x888888aa,inputA,inputB,inputC,inputD,inputE],[0x888888ff,inputA,inputB,inputC,inputD,inputE],[0x8888a8a8,inputA,inputB,inputC,inputD,inputE],[0x8888aaaa,inputA,inputB,inputC,inputD,inputE],[0x8888aaaa,0xaaaaffff,inputB,inputC,inputD,inputE],[0x8888aaaa,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x8888aaaa,inputB,0xeeeeffff,inputC,inputD,inputE],[0x8888bbbb,inputA,inputB,inputC,inputD,inputE],[0x8888f8f8,inputA,inputB,inputC,inputD,inputE],[0x8888ffff,inputA,inputB,inputC,inputD,inputE],[0x88aaaaaa,inputA,inputB,inputC,inputD,inputE],[0x88ffffff,inputA,inputB,inputC,inputD,inputE],[0x99999999,inputA,inputB,inputC,inputD,inputE],[0x99999999,inputA,0xeeeeeeee,inputC,inputD,inputE],[0xa888a888,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,0xaaaaffff,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfefefefe,inputD,inputE],[0xa8a8aaaa,inputA,inputB,inputC,inputD,inputE],[0xa8a8fcfc,inputA,inputB,inputC,inputD,inputE],[0xa8a8ffff,inputA,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputA,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xfffcfffc,inputE],[inputA,0xaaaaaaaf,inputB,inputC,inputD,inputE],[inputA,0xaaaaaaee,inputB,inputC,inputD,inputE],[inputA,0xaaaaaaff,inputB,inputC,inputD,inputE],[inputA,0xaaaaafff,inputB,inputC,inputD,inputE],[inputA,0xaaaacccc,inputB,inputC,inputD,inputE],[inputA,0xaaaaeaea,inputB,inputC,inputD,inputE],[inputA,0xaaaaeeee,inputB,inputC,inputD,inputE],[inputA,0xaaaafefe,inputB,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[inputA,0xaaafffff,inputB,inputC,inputD,inputE],[inputA,0xaaeeeeee,inputB,inputC,inputD,inputE],[inputA,0xaaffffff,inputB,inputC,inputD,inputE],[inputA,0xafffffff,inputB,inputC,inputD,inputE],[inputA,inputB,0xeaaaeaaa,inputC,inputD,inputE],[inputA,inputB,0xeac0eac0,inputC,inputD,inputE],[inputA,inputB,0xeaeaeaea,inputC,inputD,inputE],[inputA,inputB,0xeaeaeeee,inputC,inputD,inputE],[inputA,inputB,0xeaeaffff,inputC,inputD,inputE],[inputA,inputB,0xeee0eee0,inputC,inputD,inputE],[inputA,inputB,0xeeeaeeea,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xffff0011],[inputA,inputB,0xeeeeeeff,inputC,inputD,inputE],[inputA,inputB,0xeeeefefe,inputC,inputD,inputE],[inputA,inputB,0xeeeeffff,inputC,inputD,inputE],[inputA,inputB,0xeeffffff,inputC,inputD,inputE],[inputA,inputB,inputC,0xfeeefeee,inputD,inputE],[inputA,inputB,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,inputC,0xfefefefe,inputD,0xffff0101],[inputA,inputB,inputC,0xfefeffff,inputD,inputE],[inputA,inputB,inputC,inputD,0xfffefffe,inputE],[inputA,inputB,inputC,inputD,0xffff000f,0xfffff0f0],[inputA,inputB,inputC,inputD,0xffff000f,0xfffffff0],[inputA,inputB,inputC,inputD,0xffff00aa,0xffffff00],[inputA,inputB,inputC,inputD,0xffff00ff,0xffffaa00],[inputA,inputB,inputC,inputD,0xffff00ff,0xffffff00],[inputA,inputB,inputC,inputD,0xffff0fff,0xfffff000],[inputA,inputB,inputC,inputD,0xffff8888,0xfffff0f0],[inputA,inputB,inputC,0xff00ffff,0xffff00ff,0xffffff00]]
def x5s5d0g0c : List (List ℕ × List ℕ) := [([0x5b,0x3b05b,0x3905b,0x3505b,0x3185b,0x2e05b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x3805b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x3c03e,0x3e,0x2103e,0x2083e,0x2003e,0x1f83e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e,0x3e],[]),([0x4a,0x3b84a,0x4a,0x3884a,0x2584a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g0 : ∀ q (hq : q < x5s5d0.size), 0 ≤ q → q < 4 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 0 x5s5d0g0c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g4c : List (List ℕ × List ℕ) := [([0x5b,0x3c05b,0x5b,0x3905b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x72,0x3c872,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72,0x72],[]),([0x5b,0x3d05b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g4 : ∀ q (hq : q < x5s5d0.size), 4 ≤ q → q < 8 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 4 x5s5d0g4c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g8c : List (List ℕ × List ℕ) := [([0x5b,0,0,0,0,0x3b,0x3a,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x55,0x55,0x55,0x55,0x2b055,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g8 : ∀ q (hq : q < x5s5d0.size), 8 ≤ q → q < 12 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 8 x5s5d0g8c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g12c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([31,31,31,0x1181f,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d],[]),([0x3c,0x3c,0x3c,0x1e83c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c,0x3c],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g12 : ∀ q (hq : q < x5s5d0.size), 12 ≤ q → q < 16 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 12 x5s5d0g12c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g16c : List (List ℕ × List ℕ) := [([0x55,0x55,0x55,0x55,0x55,0x55,0x2b855,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55],[]),([0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x57,0x2a857],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g16 : ∀ q (hq : q < x5s5d0.size), 16 ≤ q → q < 20 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 16 x5s5d0g16c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g20c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g20 : ∀ q (hq : q < x5s5d0.size), 20 ≤ q → q < 24 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 20 x5s5d0g20c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g24c : List (List ℕ × List ℕ) := [([0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62,0x62],[]),([0x5b,0x3205b,0x3005b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g24 : ∀ q (hq : q < x5s5d0.size), 24 ≤ q → q < 28 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 24 x5s5d0g24c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g28c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g28 : ∀ q (hq : q < x5s5d0.size), 28 ≤ q → q < 32 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 28 x5s5d0g28c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g32c : List (List ℕ × List ℕ) := [([0x5b,0,0,0,0,0,0,0x35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35],[]),([0,0x5b,0x37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44,0x44],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g32 : ∀ q (hq : q < x5s5d0.size), 32 ≤ q → q < 36 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 32 x5s5d0g32c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g36c : List (List ℕ × List ℕ) := [([0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46,0x46],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g36 : ∀ q (hq : q < x5s5d0.size), 36 ≤ q → q < 40 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 36 x5s5d0g36c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g40c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g40 : ∀ q (hq : q < x5s5d0.size), 40 ≤ q → q < 44 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 40 x5s5d0g40c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g44c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34],[]),([0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35,0x35],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g44 : ∀ q (hq : q < x5s5d0.size), 44 ≤ q → q < 48 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 44 x5s5d0g44c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g48c : List (List ℕ × List ℕ) := [([0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39,0x39],[]),([0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54,0x54],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g48 : ∀ q (hq : q < x5s5d0.size), 48 ≤ q → q < 52 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 48 x5s5d0g48c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g52c : List (List ℕ × List ℕ) := [([0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65,0x65],[]),([0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68,0x68],[]),([0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59,0x59],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g52 : ∀ q (hq : q < x5s5d0.size), 52 ≤ q → q < 56 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 52 x5s5d0g52c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g56c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g56 : ∀ q (hq : q < x5s5d0.size), 56 ≤ q → q < 60 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 56 x5s5d0g56c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g60c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0,0,0,0,0,0,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g60 : ∀ q (hq : q < x5s5d0.size), 60 ≤ q → q < 64 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 60 x5s5d0g60c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g64c : List (List ℕ × List ℕ) := [([0,0x5b,0,0,0,0,0x2d,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g64 : ∀ q (hq : q < x5s5d0.size), 64 ≤ q → q < 68 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 64 x5s5d0g64c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g68c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([4,4,4,4,4,4,0x2a804,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g68 : ∀ q (hq : q < x5s5d0.size), 68 ≤ q → q < 72 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 68 x5s5d0g68c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g72c : List (List ℕ × List ℕ) := [([4,4,4,4,4,4,0x2a804,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4],[]),([0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055,0x2055],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x205b],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g72 : ∀ q (hq : q < x5s5d0.size), 72 ≤ q → q < 76 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 72 x5s5d0g72c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g76c : List (List ℕ × List ℕ) := [([0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d,0x2d],[]),([0x55,0x55,0x55,0x55,0x55,0x55,0x2055,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x86f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f,0x6f],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g76 : ∀ q (hq : q < x5s5d0.size), 76 ≤ q → q < 80 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 76 x5s5d0g76c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g80c : List (List ℕ × List ℕ) := [([0x285b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([8,8,8,8,8,8,8,8,0x3008,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8],[]),([0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b,0x405b],[]),([8,8,0x3e808,8,8,8,8,8,8,8,0x4808,8,8,8,8,8,8,8,8,8,8,8,8],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g80 : ∀ q (hq : q < x5s5d0.size), 80 ≤ q → q < 84 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 80 x5s5d0g80c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g84c : List (List ℕ × List ℕ) := [([8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,0x3808,8,8,8,8],[]),([0x384a,0x4a,0x504a,0x4a,0x4a,0x684a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a],[]),([0x405b,0x5b,0x585b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x4875,0x75,0x1875,0x5875,0x6075,0x7075,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75,0x75],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g84 : ∀ q (hq : q < x5s5d0.size), 84 ≤ q → q < 88 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 84 x5s5d0g84c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g88c : List (List ℕ × List ℕ) := [([0x785b,0x5b,0x585b,0x805b,0x885b,0x905b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x2f85b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([31,0x1101f,31,0x1081f,0xa81f,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([0x5b,0x3285b,0x5b,0x3005b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g88 : ∀ q (hq : q < x5s5d0.size), 88 ≤ q → q < 92 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 88 x5s5d0g88c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g92c : List (List ℕ × List ℕ) := [([0x60,0x33060,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60],[]),([0,0x6e,0,0x6d,0,21,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g92 : ∀ q (hq : q < x5s5d0.size), 92 ≤ q → q < 96 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 92 x5s5d0g92c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g96c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x3605b,0x5b,0x3285b,0x5b,0x3085b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825,0xf825],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g96 : ∀ q (hq : q < x5s5d0.size), 96 ≤ q → q < 100 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 96 x5s5d0g96c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g100c : List (List ℕ × List ℕ) := [([0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26,0x26],[]),([0,0x5b,0x27,0,0,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0x34,0,0x2f,0,0x2e,0,0,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x4a,0x3584a,0x4a,0x4a,0x4a,0x4a,0xd84a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a,0x4a],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g100 : ∀ q (hq : q < x5s5d0.size), 100 ≤ q → q < 104 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 100 x5s5d0g100c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g104c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0xf85b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x60,0x36860,0x60,0x60,0x60,0x60,0x10860,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60,0x60],[]),([0,0,0,0,0,0,0,0x23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g104 : ∀ q (hq : q < x5s5d0.size), 104 ≤ q → q < 108 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 104 x5s5d0g104c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g108c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g108 : ∀ q (hq : q < x5s5d0.size), 108 ≤ q → q < 112 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 108 x5s5d0g108c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g112c : List (List ℕ × List ℕ) := [([31,31,31,31,31,31,31,31,31,31,31,0xb01f,31,31,31,31,31,31,31,31,31,31],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g112 : ∀ q (hq : q < x5s5d0.size), 112 ≤ q → q < 116 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 112 x5s5d0g112c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g116c : List (List ℕ × List ℕ) := [([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([31,31,31,31,31,31,31,31,0xb81f,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([0xa81f,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[]),([31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31,31],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g116 : ∀ q (hq : q < x5s5d0.size), 116 ≤ q → q < 120 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 116 x5s5d0g116c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g120c : List (List ℕ × List ℕ) := [([31,31,31,31,31,31,0xb01f,31,31,31,31,31,31,31,31,0xe81f,31,0xf01f,31,31,31],[]),([31,31,31,31,31,31,31,31,31,31,31,31,0xc01f,31,31,31,0xd81f,31,31,31,31,31,31],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g120 : ∀ q (hq : q < x5s5d0.size), 120 ≤ q → q < 124 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 120 x5s5d0g120c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g124c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g124 : ∀ q (hq : q < x5s5d0.size), 124 ≤ q → q < 128 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 124 x5s5d0g124c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g128c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g128 : ∀ q (hq : q < x5s5d0.size), 128 ≤ q → q < 132 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 128 x5s5d0g128c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g132c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x1285b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0xf825,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25,0x25],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g132 : ∀ q (hq : q < x5s5d0.size), 132 ≤ q → q < 136 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 132 x5s5d0g132c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g136c : List (List ℕ × List ℕ) := [([0x5b,0x3a05b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x1405b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g136 : ∀ q (hq : q < x5s5d0.size), 136 ≤ q → q < 140 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 136 x5s5d0g136c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g140c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0x29,0,0,0,0,0,0,0,0,0,0x2a,0,0x2b,0,0,0],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g140 : ∀ q (hq : q < x5s5d0.size), 140 ≤ q → q < 144 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 140 x5s5d0g140c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g144c : List (List ℕ × List ℕ) := [([0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b,0x1a05b],[]),([0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x18834,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x19034,0x34,0x34,0x34,0x34,0x34],[]),([0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x34,0x19834,0x34],[]),([0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878,0x2d878],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g144 : ∀ q (hq : q < x5s5d0.size), 144 ≤ q → q < 148 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 144 x5s5d0g144c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g148c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g148 : ∀ q (hq : q < x5s5d0.size), 148 ≤ q → q < 152 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 148 x5s5d0g148c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g152c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g152 : ∀ q (hq : q < x5s5d0.size), 152 ≤ q → q < 156 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 152 x5s5d0g152c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g156c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x1205b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g156 : ∀ q (hq : q < x5s5d0.size), 156 ≤ q → q < 160 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 156 x5s5d0g156c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g160c : List (List ℕ × List ℕ) := [([0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b,0x2d87b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x3e05b,0x5b,0x5b,0x5b,0x5b,0x5b,0x3985b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g160 : ∀ q (hq : q < x5s5d0.size), 160 ≤ q → q < 164 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 160 x5s5d0g160c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g164c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0xc05b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x2485b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0xc85b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x2285b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0xf85b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g164 : ∀ q (hq : q < x5s5d0.size), 164 ≤ q → q < 168 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 164 x5s5d0g164c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g168c : List (List ℕ × List ℕ) := [([0x1005d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d],[]),([0x1185b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g168 : ∀ q (hq : q < x5s5d0.size), 168 ≤ q → q < 172 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 168 x5s5d0g168c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g172c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x2605b,0x5b,0x5b,0x5b,0x5b,0x5b,0x2805b,0x5b,0x2985b,0x5b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x2805b,0x5b,0x2a05b,0x5b,0x5b,0x5b],[]),([0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x5e,0x2885e,0x5e,0x2a05e,0x5e,0x5e],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g172 : ∀ q (hq : q < x5s5d0.size), 172 ≤ q → q < 176 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 172 x5s5d0g172c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g176c : List (List ℕ × List ℕ) := [([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x2905b,0x5b,0x2a05b,0x5b,0x5b],[]),([0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x5b,0x2d05b,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x4d,0,0,0,0,0,0x5b],[]),([0,0,0,0,0,0,0,0,0x3f,0,0,0,0,0,0,0,0x48,0,0,0,0,0,0,0,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g176 : ∀ q (hq : q < x5s5d0.size), 176 ≤ q → q < 180 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 176 x5s5d0g176c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g180c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0x3a,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x55,0x5b],[]),([0,0,0,0,0,0,0x36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x55,0x5b],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x4e,0,0,0x58,0,0,0x5b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g180 : ∀ q (hq : q < x5s5d0.size), 180 ≤ q → q < 184 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 180 x5s5d0g180c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
def x5s5d0g184c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0x38,0,0,0,0,0,0,0,0x47,0,0,0,0x4f,0,0,0,0,0,0x60],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0x57,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0g184 : ∀ q (hq : q < x5s5d0.size), 184 ≤ q → q < 186 → ¬ Reach x5s5d0[q].toFinset 5 0 0xfee8e880 := by
  have check : part x5s5d0 0xfee8e880 5 0 x5s4d0r #[] 184 x5s5d0g184c = true := by decide +kernel
  exact part_ok x5s4d0rok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0ok : correct x5s5d0 5 0 0xfee8e880 := by
  intro q hq
  have lim : q < 186 := hq
  by_cases atMid : q < 92
  ·
    by_cases atMid : q < 44
    ·
      by_cases atMid : q < 20
      ·
        by_cases atMid : q < 8
        ·
          by_cases atMid : q < 4
          ·
            exact x5s5d0g0 q hq (by omega) (by omega)
          ·
            exact x5s5d0g4 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 12
          ·
            exact x5s5d0g8 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 16
            ·
              exact x5s5d0g12 q hq (by omega) (by omega)
            ·
              exact x5s5d0g16 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 32
        ·
          by_cases atMid : q < 24
          ·
            exact x5s5d0g20 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 28
            ·
              exact x5s5d0g24 q hq (by omega) (by omega)
            ·
              exact x5s5d0g28 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 36
          ·
            exact x5s5d0g32 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 40
            ·
              exact x5s5d0g36 q hq (by omega) (by omega)
            ·
              exact x5s5d0g40 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 68
      ·
        by_cases atMid : q < 56
        ·
          by_cases atMid : q < 48
          ·
            exact x5s5d0g44 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 52
            ·
              exact x5s5d0g48 q hq (by omega) (by omega)
            ·
              exact x5s5d0g52 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 60
          ·
            exact x5s5d0g56 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 64
            ·
              exact x5s5d0g60 q hq (by omega) (by omega)
            ·
              exact x5s5d0g64 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 80
        ·
          by_cases atMid : q < 72
          ·
            exact x5s5d0g68 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 76
            ·
              exact x5s5d0g72 q hq (by omega) (by omega)
            ·
              exact x5s5d0g76 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 84
          ·
            exact x5s5d0g80 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 88
            ·
              exact x5s5d0g84 q hq (by omega) (by omega)
            ·
              exact x5s5d0g88 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 140
    ·
      by_cases atMid : q < 116
      ·
        by_cases atMid : q < 104
        ·
          by_cases atMid : q < 96
          ·
            exact x5s5d0g92 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 100
            ·
              exact x5s5d0g96 q hq (by omega) (by omega)
            ·
              exact x5s5d0g100 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 108
          ·
            exact x5s5d0g104 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 112
            ·
              exact x5s5d0g108 q hq (by omega) (by omega)
            ·
              exact x5s5d0g112 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 128
        ·
          by_cases atMid : q < 120
          ·
            exact x5s5d0g116 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 124
            ·
              exact x5s5d0g120 q hq (by omega) (by omega)
            ·
              exact x5s5d0g124 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 132
          ·
            exact x5s5d0g128 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 136
            ·
              exact x5s5d0g132 q hq (by omega) (by omega)
            ·
              exact x5s5d0g136 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 164
      ·
        by_cases atMid : q < 152
        ·
          by_cases atMid : q < 144
          ·
            exact x5s5d0g140 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 148
            ·
              exact x5s5d0g144 q hq (by omega) (by omega)
            ·
              exact x5s5d0g148 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 156
          ·
            exact x5s5d0g152 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 160
            ·
              exact x5s5d0g156 q hq (by omega) (by omega)
            ·
              exact x5s5d0g160 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 176
        ·
          by_cases atMid : q < 168
          ·
            exact x5s5d0g164 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 172
            ·
              exact x5s5d0g168 q hq (by omega) (by omega)
            ·
              exact x5s5d0g172 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 180
          ·
            exact x5s5d0g176 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 184
            ·
              exact x5s5d0g180 q hq (by omega) (by omega)
            ·
              exact x5s5d0g184 q hq (by omega) (by omega)
def x5s5d0r : Array (List Word) := #[[10,inputA,inputB,inputC,inputD,inputE],[12,inputA,inputB,inputC,inputD,inputE],[15,0xaaaaaaa0,inputB,inputC,inputD,inputE],[15,inputA,0xccccccc0,inputC,inputD,inputE],[15,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[15,inputA,inputB,inputC,inputD,inputE],[15,inputA,0xcccccccf,inputC,inputD,inputE],[15,0xaaaaaaaf,inputB,inputC,inputD,inputE],[0x88,inputA,inputB,inputC,inputD,inputE],[0xa0,inputA,inputB,inputC,inputD,inputE],[0xaa,0xaaaaaa00,inputB,inputC,inputD,inputE],[0xaa,inputA,inputB,inputC,0xff000000,0xffffff00],[0xaa,inputA,inputB,inputC,inputD,inputE],[0xaa,0xaaaaaaff,inputB,inputC,inputD,inputE],[0xcc,inputA,inputB,inputC,0xff000000,0xffffff00],[0xcc,inputA,inputB,inputC,inputD,inputE],[0xee,inputA,inputB,inputC,inputD,inputE],[0xf0,inputA,inputB,inputC,0xff000000,0xffffff00],[0xf0,inputA,inputB,inputC,inputD,inputE],[0xff,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xff,0xaa00aa00,inputB,inputC,0xffaaffaa,inputE],[0xff,inputA,0xcccccc88,inputC,inputD,inputE],[0xff,inputA,inputB,0xf0f0f0a0,inputD,inputE],[0xff,inputA,inputB,inputC,0xff000000,0xffffff00],[0xff,inputA,inputB,inputC,0xff0000ff,0xffffff00],[0xff,inputA,inputB,inputC,inputD,inputE],[0xaaa,inputA,inputB,inputC,inputD,inputE],[0xccc,inputA,inputB,inputC,inputD,inputE],[0xf00,inputA,inputB,inputC,inputD,inputE],[0xfff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfff,inputA,inputB,inputC,inputD,inputE],[0x7f7f,inputA,inputB,inputC,inputD,0xffff8080],[0x8080,inputA,inputB,inputC,inputD,inputE],[0x8800,inputA,inputB,inputC,inputD,inputE],[0x8888,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x8888,inputA,inputB,inputC,inputD,inputE],[0x8888,inputA,0xcccceeee,inputC,inputD,inputE],[0xa0a0,inputA,inputB,inputC,inputD,inputE],[0xa8a8,inputA,inputB,inputC,inputD,inputE],[0xaa00,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0x55550000,0xaaaa0000,inputB,inputC,inputD],[0xaaaa,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xaaaa,0xaaaa0000,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xaaaa,0xaaaa8888,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[0xaaaa,inputA,0xcccc0000,inputC,inputD,0xffffcccc],[0xaaaa,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaaeeee,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa,inputB,0xeaeaeaea,inputC,inputD,inputE],[0xc0c0,inputA,inputB,inputC,inputD,inputE],[0xcc00,inputA,inputB,inputC,inputD,inputE],[0xcccc,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xcccc,inputA,0xcccc0000,inputC,inputD,inputE],[0xcccc,inputA,inputB,inputC,inputD,inputE],[0xcccc,inputA,0xcccceeee,inputC,inputD,inputE],[0xe0e0,inputA,inputB,inputC,inputD,inputE],[0xeaea,inputA,inputB,inputC,inputD,inputE],[0xee00,inputA,inputB,inputC,inputD,inputE],[0xeeee,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xeeee,inputA,inputB,inputC,inputD,inputE],[0xf000,inputA,inputB,inputC,inputD,inputE],[0xf0f0,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xf0f0,inputA,inputB,inputC,inputD,inputE],[0xfefe,inputA,inputB,inputC,inputD,inputE],[0xff00,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xff00,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xff00,inputA,inputB,inputC,0xff000000,inputE],[0xff00,inputA,inputB,inputC,0xff000000,0xffffff00],[0xff00,inputA,inputB,inputC,inputD,inputE],[0xff00,inputA,inputB,inputC,0xff00ffff,inputE],[0xfff0,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xffff,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0xffff,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xffff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xffff,inputA,inputB,0xf0f0e0e0,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfe00fe00,inputE],[0xffff,inputA,inputB,inputC,0xfefe0000,inputD],[0xffff,inputA,inputB,inputC,0xff000000,0xffffff00],[0xffff,inputA,inputB,inputC,0xff00ee00,inputE],[0xffff,inputA,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffff8080],[0xffff,inputA,inputB,inputC,0xff80ff80,inputE],[0xffff,inputA,inputB,inputC,0xff88ff00,inputE],[0xffff,inputA,inputB,0xf8f8f0f0,inputD,inputE],[0xffff,inputB,0xeaaaeaaa,inputC,inputD,inputE],[0x10001,inputA,inputB,inputC,inputD,inputE],[0x30003,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xaaaaa,inputA,inputB,inputC,inputD,inputE],[0xccccc,inputA,inputB,inputC,inputD,inputE],[0xf0000,inputA,inputB,inputC,inputD,0xfff00000],[0xf0000,inputA,inputB,inputC,inputD,inputE],[0xf000f,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xf000f,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfffff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfffff,inputA,inputB,inputC,inputD,inputE],[0x888888,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0,inputA,inputB,inputC,inputD,inputE],[0xaa0000,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa,0xaa000000,inputB,inputC,inputD,inputE],[0xaaaaaa,0xaa00aa00,inputB,inputC,inputD,inputE],[0xaaaaaa,0xaaaa0000,inputB,inputC,inputD,inputE],[0xaaaaaa,inputA,inputB,inputC,0xff000000,0xffffff00],[0xaaaaaa,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa,0xaaffffff,inputB,inputC,inputD,inputE],[0xaaaaaa,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaaaaaa,inputB,inputC,0xfafafafa,inputD,inputE],[0xaaffaa,inputA,inputB,inputC,inputD,inputE],[0xcccccc,inputA,inputB,inputC,0xff000000,0xffffff00],[0xcccccc,inputA,inputB,inputC,inputD,inputE],[0xcccccc,inputA,0xeeeeeeee,inputC,inputD,inputE],[0xeeeeee,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0,inputA,inputB,0xf0000000,inputD,inputE],[0xf0f0f0,inputA,inputB,0xf000f000,inputD,inputE],[0xf0f0f0,inputA,inputB,inputC,0xff000000,0xffffff00],[0xf0f0f0,inputA,inputB,inputC,inputD,inputE],[0xff0000,inputA,inputB,inputC,0xff000000,inputD],[0xff0000,inputA,inputB,inputC,inputD,inputE],[0xff00ff,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xff00ff,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0xff00ff,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,0xffff8080],[0xff00ff,inputB,0xeaaaeaaa,inputC,inputD,inputE],[0xffff00,0xffffff,inputA,inputB,inputC,0xff000000],[0xffff00,inputA,inputB,inputC,0xff000000,inputD],[0xffff00,inputA,inputB,inputC,0xff000000,0xffffff00],[0xffff00,inputA,inputB,inputC,inputD,inputE],[0xffffff,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xffffff,0xaa00aa00,inputB,inputC,0xffaaffaa,inputE],[0xffffff,inputA,inputB,inputC,0xff000000,0xffffff00],[0xffffff,inputA,inputB,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xfaf0f0f0,inputD,inputE],[0xffffff,inputA,0xeecccccc,inputC,inputD,inputE],[0x1010101,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x1010101,inputA,inputB,inputC,inputD,inputE],[0x1110111,inputA,inputB,inputC,inputD,inputE],[0x3030303,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0x5050505,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x5050505,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x7070707,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xaaaaaaa,0xfffffff,inputB,inputC,inputD,inputE],[0xaaaaaaa,inputA,inputB,inputC,inputD,inputE],[0xaaaaaaa,inputB,0xf0000000,inputC,inputD,inputE],[0xaaaaaaa,inputB,0xf000f000,inputC,inputD,inputE],[0xccccccc,0xfffffff,inputA,inputC,inputD,inputE],[0xccccccc,inputA,inputB,inputC,inputD,inputE],[0xccccccc,inputA,0xf0000000,inputC,inputD,inputE],[0xccccccc,inputA,0xf000f000,inputC,inputD,inputE],[0xf00ff00,inputA,inputB,0xf0000000,inputC,inputE],[0xf00ff00,inputA,inputB,0xf000f000,inputC,inputE],[0xf00ff00,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0f0f,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,0xffff8080],[0xf0f0f0f,inputB,0xeaaaeaaa,inputC,inputD,inputE],[0xfff0000,inputA,inputB,0xf0000000,inputC,inputD],[0xfff0000,inputA,inputB,inputC,inputD,inputE],[0xfff0fff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfffffff,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0xfffffff,inputA,inputB,inputC,inputD,inputE],[0xfffffff,inputA,inputC,0xfccccccc,inputD,inputE],[0xfffffff,inputB,inputC,0xfaaaaaaa,inputD,inputE],[0x11111111,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x11111111,inputA,inputB,inputC,inputD,inputE],[0x11151115,inputA,inputB,inputC,inputD,inputE],[0x111f111f,inputA,inputB,inputC,inputD,inputE],[0x15151515,inputA,inputB,inputC,inputD,inputE],[0x153f153f,inputA,inputB,inputC,inputD,inputE],[0x15551555,inputA,inputB,inputC,inputD,inputE],[0x15551555,inputB,0xeaaaeaaa,inputC,inputD,inputE],[0x1f1f1f1f,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x33333333,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x33333333,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,0xffff8080],[0x33333333,inputB,0xeaaaeaaa,inputC,inputD,inputE],[0x4444cccc,inputA,inputB,inputC,inputD,inputE],[0x5050f0f0,inputA,inputB,inputC,inputD,inputE],[0x5500ff00,inputA,inputB,inputC,inputD,inputE],[0x55550000,inputA,inputB,inputC,inputD,inputE],[0x55555555,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x55555555,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,0xffff8080],[0x55555555,inputB,0xeaaaeaaa,inputC,inputD,inputE],[0x5555ffff,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0x5555ffff,inputA,inputB,inputC,inputD,inputE],[0x55575557,0xaaa8aaa8,inputB,inputC,inputD,inputE],[0x55575557,inputA,inputB,inputC,inputD,inputE],[0x57575757,inputA,inputB,inputC,inputD,inputE],[0x57775777,inputA,inputB,inputC,inputD,inputE],[0x5f5f5f5f,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x77777777,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x77777777,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x77777777,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0x77777777,inputA,inputB,inputC,inputD,inputE],[0x77777777,inputA,inputB,inputC,inputD,0xffff8080],[0x777f777f,inputA,inputB,inputC,inputD,inputE],[0x7f7f7f7f,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x7f7f7f7f,inputA,inputB,inputC,inputD,inputE],[0x7f7f7f7f,inputA,inputB,inputC,inputD,0xffff8080],[0x7fff7fff,inputA,inputB,inputC,inputD,inputE],[0x80008000,inputA,inputB,inputC,inputD,inputE],[0x80800000,inputA,inputB,inputC,inputD,inputE],[0x80808080,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,0xffff8080],[0x80808080,inputA,inputB,inputC,0xff80ff80,inputE],[0x80808080,inputA,inputB,0xf8f8f8f8,inputD,inputE],[0x80808888,inputA,inputB,inputC,inputD,inputE],[0x8080a0a0,inputA,inputB,inputC,inputD,inputE],[0x8080f0f0,inputA,inputB,inputC,inputD,inputE],[0x8080ffff,inputA,inputB,inputC,inputD,inputE],[0x88000000,inputA,inputB,inputC,inputD,inputE],[0x88008800,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88008800,inputA,inputB,inputC,inputD,inputE],[0x8800aa00,inputA,inputB,inputC,inputD,inputE],[0x8800ff00,inputA,inputB,inputC,inputD,inputE],[0x88808880,inputA,inputB,inputC,inputD,inputE],[0x88880000,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88880000,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0x88880000,inputA,inputB,inputC,inputD,inputE],[0x88880000,inputA,inputB,inputC,0xff88ff00,inputE],[0x88880000,inputA,inputB,0xf8f8f0f0,inputD,inputE],[0x88888800,inputA,inputB,inputC,inputD,inputE],[0x88888888,0x8888ffff,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x88888888,0xa0a0a0a0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xa2a2a2a2,inputB,inputC,inputD,inputE],[0x88888888,0xaa00aa00,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xaaa0aaa0,inputB,inputC,inputD,inputE],[0x88888888,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0x88888888,0xaaaa0000,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xaaaaaa00,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xc4c4c4c4,inputC,inputD,inputE],[0x88888888,inputA,0xccc0ccc0,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0x88888888,inputA,inputB,inputC,0xff000000,0xffffff00],[0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffff8080],[0x88888888,inputA,inputB,inputC,0xff80ff80,inputE],[0x88888888,inputA,0xccccccff,inputC,inputD,inputE],[0x88888888,inputA,0xcccceeee,inputC,inputD,inputE],[0x88888888,inputA,0xecececec,inputC,inputD,inputE],[0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xaaaaaaff,inputB,inputC,inputD,inputE],[0x88888888,0xaaaaeeee,inputB,inputC,inputD,inputE],[0x88888888,0xaaaaffff,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xbbbbbbbb,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xc0c0c0c0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xcc00cc00,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xcccc0000,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,inputB,0xeaeaeaea,inputC,inputD,inputE],[0x88888888,inputB,0xeeeeaaaa,inputC,inputD,inputE],[0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xe0e0e0e0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xee00ee00,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeee0000,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xeeeeffff,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf000f000,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf0f00000,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf0f0ffff,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf3f3f3f3,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf7f7f7f7,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfcfcfcfc,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xff000000,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xff00ffff,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xff88ff88,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffaaffaa,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffccffcc,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffeeffee,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffff8888],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffaaaa],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffcccc],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffeeee],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xfffff0f0],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffff00],[0x888888cc,inputA,inputB,inputC,inputD,inputE],[0x888888ff,inputA,inputB,inputC,inputD,inputE],[0x8888aaaa,0xaaaa0000,inputB,inputC,inputD,inputE],[0x8888aaaa,inputA,inputB,inputC,inputD,inputE],[0x8888aaaa,0xaaaaffff,inputB,inputC,inputD,inputE],[0x8888aaaa,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x8888aaaa,inputB,0xeeeeffff,inputC,inputD,inputE],[0x8888cccc,inputA,inputB,inputC,inputD,inputE],[0x8888cccc,inputA,0xccccffff,inputC,inputD,inputE],[0x8888cccc,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x8888cccc,inputA,0xeeeeffff,inputC,inputD,inputE],[0x8888ffff,inputA,inputB,inputC,inputD,inputE],[0x88cccccc,inputA,inputB,inputC,inputD,inputE],[0x88ffffff,inputA,inputB,inputC,inputD,inputE],[0xa0000000,inputA,inputB,inputC,inputD,inputE],[0xa000a000,inputA,inputB,inputC,inputD,inputE],[0xa0a00000,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xa0a00000,inputA,inputB,inputC,inputD,inputE],[0xa0a08080,inputA,inputB,inputC,inputD,inputE],[0xa0a0a000,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xa0a0a0a0,0xaaaa8888,inputB,inputC,inputD,inputE],[0xa0a0a0a0,0xaaaaaa00,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,0xff000000,0xffffff00],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,0xf8f8f8f8,inputD,inputE],[0xa0a0a0a0,inputA,inputB,0xfafafafa,inputD,inputE],[0xa0a0a0a0,0xaaaaaaff,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputB,0xeaeaeaea,inputC,inputD,inputE],[0xa0a0a0a0,inputB,0xeeeeeeee,0xfafafafa,inputD,inputE],[0xa0a0a0a0,inputB,inputC,0xfafafafa,inputD,inputE],[0xa0a0a0f0,inputA,inputB,inputC,inputD,inputE],[0xa0a0aaaa,inputA,inputB,inputC,inputD,inputE],[0xa0a0e0e0,inputA,inputB,inputC,inputD,inputE],[0xa0a0f0f0,inputA,inputB,inputC,inputD,inputE],[0xa0f0f0f0,inputA,inputB,inputC,inputD,inputE],[0xa2a2a2a2,inputA,inputB,inputC,inputD,inputE],[0xa800a800,inputA,inputB,inputC,inputD,inputE],[0xa888a888,inputA,inputB,inputC,inputD,inputE],[0xa8a80000,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,0xaa00aa00,inputB,inputC,inputD,inputE],[0xa8a8a8a8,0xaaaa0000,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputA,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,0xaaaaffff,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfafafafa,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfefefefe,inputD,inputE],[0xa8a8fcfc,inputA,inputB,inputC,inputD,inputE],[0xa8a8ffff,inputA,inputB,inputC,inputD,inputE],[0xaa000000,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xaa000000,inputA,inputB,inputC,0xff000000,0xffffff00],[0xaa000000,inputA,inputB,inputC,inputD,inputE],[0xaa000000,inputA,inputB,0xfaf0f0f0,inputD,inputE],[0xaa000000,inputA,0xeecccccc,inputC,inputD,inputE],[0xaa008800,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,0xaaaa0000,inputB,inputC,inputD,0xffffaaaa],[0xaa00aa00,0xaaaa8888,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,0xff000000,0xffffff00],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,0xffaaffaa,inputE],[0xaa00aa00,inputB,inputC,inputD,0xffaaaaaa,inputE],[0xaa00aa00,inputB,inputC,inputD,0xffaaffaa,inputE],[0xaa00aaaa,inputA,inputB,inputC,inputD,inputE],[0xaa00aaff,inputA,inputB,inputC,inputD,inputE],[0xaa00ee00,inputA,inputB,inputC,inputD,inputE],[0xaa00ff00,inputA,inputB,inputC,inputD,inputE],[0xaaa00000,inputA,inputB,inputC,inputD,inputE],[0xaaa0aaa0,inputA,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputA,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xfffcfffc,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,0xfff00000],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,0xffff8888],[0xaaaa0000,inputA,inputB,inputC,inputD,0xffffaaaa],[0xaaaa0000,0xaaaaffff,inputB,inputC,inputD,0xffffaaaa],[0xaaaa0000,0xc0c0c0c0,inputB,inputC,inputD,0xffffaaaa],[0xaaaa0000,0xcc00cc00,inputB,inputC,inputD,0xffffaaaa],[0xaaaa0000,0xcccc0000,inputB,inputC,inputD,0xffffaaaa],[0xaaaa0000,0xcccc8888,inputB,inputC,inputD,0xffffaaaa],[0xaaaa0000,inputB,0xccccffff,inputC,inputD,0xffffaaaa],[0xaaaa0000,inputB,0xeeeeaaaa,inputC,inputD,inputE],[0xaaaa0000,inputB,0xeeeecccc,inputC,inputD,0xffffaaaa],[0xaaaa0000,inputB,0xeeeeeeee,inputC,inputD,0xffffaaaa],[0xaaaa0000,inputB,0xf000f000,inputC,inputD,0xffffaaaa],[0xaaaa0000,inputB,0xf0f00000,inputC,inputD,0xffffaaaa],[0xaaaa0000,inputB,0xf0f0a0a0,inputC,inputD,0xffffaaaa],[0xaaaa0000,inputB,inputC,0xf0f0ffff,inputD,0xffffaaaa],[0xaaaa0000,inputB,inputC,0xfafaf0f0,inputD,0xffffaaaa],[0xaaaa0000,inputB,inputC,0xfafafafa,inputD,0xffffaaaa],[0xaaaa0000,inputB,inputC,0xfcfcfcfc,inputD,0xffffaaaa],[0xaaaa0000,inputB,inputC,0xff000000,inputD,0xffffaaaa],[0xaaaa0000,inputB,inputC,0xff00aa00,inputD,0xffffaaaa],[0xaaaa0000,inputB,inputC,inputD,0xff00ffff,0xffffaaaa],[0xaaaa0000,inputB,inputC,inputD,0xffaaaaaa,inputE],[0xaaaa0000,inputB,inputC,inputD,0xffaaff00,0xffffaaaa],[0xaaaa0000,inputB,inputC,inputD,0xffaaffaa,0xffffaaaa],[0xaaaa0000,inputB,inputC,inputD,0xffccffcc,0xffffaaaa],[0xaaaa0000,inputB,inputC,inputD,0xfff0fff0,0xffffaaaa],[0xaaaa0000,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaa0000,inputB,inputC,inputD,0xffffaaaa,0xffffcccc],[0xaaaa0000,inputB,inputC,inputD,0xffffaaaa,0xffffeeee],[0xaaaa0000,inputB,inputC,inputD,0xffffaaaa,0xfffff0f0],[0xaaaa0000,inputB,inputC,inputD,0xffffaaaa,0xfffffafa],[0xaaaa0000,inputB,inputC,inputD,0xffffaaaa,0xffffff00],[0xaaaa0000,inputB,inputC,inputD,0xffffaaaa,0xffffffaa],[0xaaaa8888,inputA,inputB,inputC,inputD,inputE],[0xaaaa8888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaaaa8888,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaaa000,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa00,inputA,inputB,inputC,0xff000000,0xffffff00],[0xaaaaaa00,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa00,inputB,inputC,inputD,0xffaaffaa,inputE],[0xaaaaaa00,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaaaaa0,inputA,inputB,inputC,inputD,inputE],[0xaaaaaaa0,inputB,inputC,inputD,inputE,0xfffffff0],[inputA,0xaaaaaaaf,inputB,inputC,inputD,inputE],[inputA,0xaaaaaaff,inputB,inputC,0xff000000,0xffffff00],[inputA,0xaaaaaaff,inputB,inputC,inputD,inputE],[inputA,0xaaaaafff,inputB,inputC,inputD,inputE],[inputA,0xaaaacccc,inputB,inputC,inputD,inputE],[inputA,0xaaaaeeee,inputB,inputC,inputD,inputE],[inputA,0xaaaaffff,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[inputA,0xaaaaffff,0xcccc0000,inputC,inputD,0xffffcccc],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[inputA,0xaaafffff,inputB,inputC,inputD,inputE],[inputA,0xaaff0000,inputB,inputC,inputD,inputE],[inputA,0xaaffffff,inputB,inputC,0xff000000,0xffffff00],[inputA,0xaaffffff,inputB,inputC,inputD,inputE],[inputA,0xafffffff,inputB,inputC,inputD,inputE],[inputA,0xb0b0b0b0,inputB,inputC,inputD,inputE],[inputA,0xbb00bb00,inputB,inputC,inputD,inputE],[inputA,0xbbbb0000,inputB,inputC,inputD,inputE],[inputA,0xbbbbbbbb,inputB,inputC,inputD,inputE],[inputA,0xc0000000,inputB,inputC,inputD,inputE],[inputA,0xc000c000,inputB,inputC,inputD,inputE],[inputA,0xc0c00000,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,0xff000000,0xffffff00],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,0xf8f8f8f8,inputD,inputE],[inputA,0xc0c0c0c0,inputB,0xfcfcfcfc,inputD,inputE],[inputA,0xc0c0c0c0,inputC,0xfcfcfcfc,inputD,inputE],[inputA,0xc0c0cccc,inputB,inputC,inputD,inputE],[inputA,0xc0c0e0e0,inputB,inputC,inputD,inputE],[inputA,0xc0c0eaea,inputB,inputC,inputD,inputE],[inputA,0xc0c0f0f0,inputB,inputC,inputD,inputE],[inputA,0xc4c4c4c4,inputB,inputC,inputD,inputE],[inputA,0xc8c8c8c8,inputB,inputC,inputD,inputE],[inputA,0xc8c8c8c8,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xcc000000,inputB,inputC,0xff000000,0xffffff00],[inputA,0xcc000000,inputB,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,0xff000000,0xffffff00],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xcc00cccc,inputB,inputC,inputD,inputE],[inputA,0xcc00ee00,inputB,inputC,inputD,inputE],[inputA,0xcc00ff00,inputB,inputC,inputD,inputE],[inputA,0xcc888888,inputB,inputC,inputD,inputE],[inputA,0xcc88cc88,inputB,inputC,inputD,inputE],[inputA,0xccc00000,inputB,inputC,inputD,inputE],[inputA,0xccc0ccc0,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,0xfff00000],[inputA,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,0xffff8888],[inputA,0xcccc0000,inputB,inputC,inputD,0xffffcccc],[inputA,0xcccc0000,inputC,inputD,inputE,0xffffcccc],[inputA,0xcccc8888,inputB,inputC,inputD,inputE],[inputA,0xccccaaaa,inputB,inputC,inputD,inputE],[inputA,0xccccc000,inputB,inputC,inputD,inputE],[inputA,0xcccccc00,inputB,inputC,0xff000000,0xffffff00],[inputA,0xcccccc00,inputB,inputC,inputD,inputE],[inputA,0xcccccc88,inputB,inputC,inputD,inputE],[inputA,0xcccccc88,inputC,inputD,inputE,0xffffffaa],[inputA,0xccccccc0,inputB,inputC,inputD,inputE],[inputA,0xccccccc0,inputC,inputD,inputE,0xfffffff0],[inputA,inputB,0xcccccccf,inputC,inputD,inputE],[inputA,inputB,0xccccccee,inputC,inputD,inputE],[inputA,inputB,0xccccccff,inputC,0xff000000,0xffffff00],[inputA,inputB,0xccccccff,inputC,inputD,inputE],[inputA,inputB,0xcccccfff,inputC,inputD,inputE],[inputA,inputB,0xcccceeee,inputC,inputD,inputE],[inputA,inputB,0xccccffff,inputC,inputD,inputE],[inputA,inputB,0xcccfffff,inputC,inputD,inputE],[inputA,inputB,0xcceeeeee,inputC,inputD,inputE],[inputA,inputB,0xccffffff,inputC,0xff000000,0xffffff00],[inputA,inputB,0xccffffff,inputC,inputD,inputE],[inputA,inputB,0xcfffffff,inputC,inputD,inputE],[inputA,inputB,0xddddffff,inputC,inputD,inputE],[inputA,inputB,0xe0e00000,inputC,inputD,inputE],[inputA,inputB,0xe0e0a0a0,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,0xfafafafa,inputD,inputE],[inputA,inputB,0xe0e0e0e0,0xfefefefe,inputD,inputE],[inputA,inputB,0xe0e0f0f0,inputC,inputD,inputE],[inputA,inputB,0xea00ea00,inputC,inputD,inputE],[inputA,inputB,0xeaaaeaaa,inputC,inputD,inputE],[inputA,inputB,0xeac0eac0,inputC,inputD,inputE],[inputA,inputB,0xeaea0000,inputC,inputD,inputE],[inputA,inputB,0xeaeaeaea,inputC,inputD,inputE],[inputA,inputB,0xeaeaffff,inputC,inputD,inputE],[inputA,inputB,0xecececec,inputC,inputD,inputE],[inputA,inputB,0xee000000,inputC,inputD,inputE],[inputA,inputB,0xee00aa00,inputC,inputD,inputE],[inputA,inputB,0xee00ee00,inputC,inputD,inputE],[inputA,inputB,0xee00ff00,inputC,inputD,inputE],[inputA,inputB,0xeecccccc,inputC,inputD,inputE],[inputA,inputB,0xeecceecc,inputC,inputD,inputE],[inputA,inputB,0xeee0eee0,inputC,inputD,inputE],[inputA,inputB,0xeeeaeeea,inputC,inputD,inputE],[inputA,inputB,0xeeee0000,0xf0f00000,inputC,inputD],[inputA,inputB,0xeeee0000,inputC,0xff000000,inputD],[inputA,inputB,0xeeee0000,inputC,inputD,inputE],[inputA,inputB,0xeeee0000,inputC,inputD,0xffffaaaa],[inputA,inputB,0xeeee0000,inputC,inputD,0xffffcccc],[inputA,inputB,0xeeeeaaaa,inputC,inputD,inputE],[inputA,inputB,0xeeeecccc,inputC,inputD,inputE],[inputA,inputB,0xeeeeeecc,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,0xf000f000,0xfff0fff0,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfe00fe00,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfefe0000,inputD],[inputA,inputB,0xeeeeeeee,inputC,0xff000000,0xffffff00],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeff,inputC,inputD,inputE],[inputA,inputB,0xeeeeffff,inputC,inputD,inputE],[inputA,inputB,0xeeffffff,inputC,inputD,inputE],[inputA,inputB,0xf0000000,inputC,0xff000000,0xffffff00],[inputA,inputB,0xf0000000,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,0xff000000,0xffffff00],[inputA,inputB,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,0xfff0fff0,inputE],[inputA,inputB,0xf000f000,inputD,0xfff0fff0,inputE],[inputA,inputB,0xf000f0f0,inputC,inputD,inputE],[inputA,inputB,0xf000ff00,inputC,inputD,inputE],[inputA,inputB,0xf000ffff,inputC,inputD,inputE],[inputA,inputB,0xf0a0a0a0,inputC,inputD,inputE],[inputA,inputB,0xf0a0f0a0,inputC,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,0xfffff000],[inputA,inputB,0xf0f08080,inputC,inputD,inputE],[inputA,inputB,0xf0f0a0a0,inputC,inputD,inputE],[inputA,inputB,0xf0f0c0c0,inputC,inputD,inputE],[inputA,inputB,0xf0f0e0e0,inputC,inputD,inputE],[inputA,inputB,0xf0f0e0e0,inputD,inputE,0xffffeeee],[inputA,inputB,0xf0f0f000,inputC,0xff000000,0xffffff00],[inputA,inputB,0xf0f0f000,inputC,inputD,inputE],[inputA,inputB,0xf0f0f0a0,inputC,inputD,inputE],[inputA,inputB,0xf0f0f0a0,inputD,inputE,0xffffffaa],[inputA,inputB,inputC,0xf0f0f0fa,inputD,inputE],[inputA,inputB,inputC,0xf0f0f0ff,0xff000000,0xffffff00],[inputA,inputB,inputC,0xf0f0f0ff,inputD,inputE],[inputA,inputB,inputC,0xf0f0f8f8,inputD,inputE],[inputA,inputB,inputC,0xf0f0fafa,inputD,inputE],[inputA,inputB,inputC,0xf0f0fcfc,inputD,inputE],[inputA,inputB,inputC,0xf0f0fefe,inputD,inputE],[inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[inputA,inputB,inputC,0xf0fafafa,inputD,inputE],[inputA,inputB,inputC,0xf0ffffff,0xff000000,0xffffff00],[inputA,inputB,inputC,0xf0ffffff,inputD,inputE],[inputA,inputB,inputC,0xf300f300,inputD,inputE],[inputA,inputB,inputC,0xf3f30000,inputD,inputE],[inputA,inputB,inputC,0xf3f3f3f3,inputD,inputE],[inputA,inputB,inputC,0xf5f5ffff,inputD,inputE],[inputA,inputB,inputC,0xf700f700,inputD,inputE],[inputA,inputB,inputC,0xf7f70000,inputD,inputE],[inputA,inputB,inputC,0xf7f7f7f7,inputD,inputE],[inputA,inputB,inputC,0xf800f800,inputD,inputE],[inputA,inputB,inputC,0xf888f888,inputD,inputE],[inputA,inputB,inputC,0xf8f80000,inputD,inputE],[inputA,inputB,inputC,0xf8f8f0f0,inputD,inputE],[inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[inputA,inputB,inputC,0xf8f8fafa,inputD,inputE],[inputA,inputB,inputC,0xf8f8ffff,inputD,inputE],[inputA,inputB,inputC,0xfa00fa00,inputD,inputE],[inputA,inputB,inputC,0xfaaaaaaa,inputD,inputE],[inputA,inputB,inputC,0xfaaafaaa,inputD,inputE],[inputA,inputB,inputC,0xfaf0f0f0,inputD,inputE],[inputA,inputB,inputC,0xfaf0faf0,inputD,inputE],[inputA,inputB,inputC,0xfafa0000,inputD,inputE],[inputA,inputB,inputC,0xfafaf0f0,inputD,inputE],[inputA,inputB,inputC,0xfafaf8f8,inputD,inputE],[inputA,inputB,inputC,0xfafafaf0,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,0xff000000,0xffffff00],[inputA,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,inputC,0xfafafaff,inputD,inputE],[inputA,inputB,inputC,0xfafafefe,inputD,inputE],[inputA,inputB,inputC,0xfafaffff,inputD,inputE],[inputA,inputB,inputC,0xfaffffff,inputD,inputE],[inputA,inputB,inputC,0xfbfbfbfb,inputD,inputE],[inputA,inputB,inputC,0xfc00fc00,inputD,inputE],[inputA,inputB,inputC,0xfccccccc,inputD,inputE],[inputA,inputB,inputC,0xfcccfccc,inputD,inputE],[inputA,inputB,inputC,0xfcfc0000,inputD,inputE],[inputA,inputB,inputC,0xfcfcf0f0,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,0xff000000,0xffffff00],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,inputC,0xfcfcfefe,inputD,inputE],[inputA,inputB,inputC,0xfcfcffff,inputD,inputE],[inputA,inputB,inputC,0xfe00fe00,0xfefefefe,inputE],[inputA,inputB,inputC,0xfe00fe00,inputD,inputE],[inputA,inputB,inputC,0xfeeefeee,inputD,inputE],[inputA,inputB,inputC,0xfefe0000,0xfefefefe,inputD],[inputA,inputB,inputC,0xfefe0000,inputD,inputE],[inputA,inputB,inputC,0xfefef0f0,inputD,inputE],[inputA,inputB,inputC,0xfefefafa,inputD,inputE],[inputA,inputB,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,inputC,0xfefeffff,inputD,inputE],[inputA,inputB,inputC,0xff000000,0xff0000ff,0xffffff00],[inputA,inputB,inputC,0xff000000,inputD,inputE],[inputA,inputB,inputC,0xff000000,inputD,0xfffff000],[inputA,inputB,inputC,0xff000000,inputD,0xffffff00],[inputA,inputB,inputC,0xff000000,0xff00ffff,0xffffff00],[inputA,inputB,inputC,0xff000000,0xffaaaaaa,0xffffff00],[inputA,inputB,inputC,0xff000000,0xffaaffaa,0xffffff00],[inputA,inputB,inputC,0xff000000,0xffcccccc,0xffffff00],[inputA,inputB,inputC,0xff000000,0xffccffcc,0xffffff00],[inputA,inputB,inputC,0xff000000,0xfff0f0f0,0xffffff00],[inputA,inputB,inputC,0xff000000,0xfff0fff0,0xffffff00],[inputA,inputB,inputC,0xff000000,inputE,0xffffff00],[inputA,inputB,inputC,0xff000000,0xffff00ff,0xffffff00],[inputA,inputB,inputC,0xff000000,0xffffff00,0xffffffaa],[inputA,inputB,inputC,0xff000000,0xffffff00,0xffffffcc],[inputA,inputB,inputC,0xff000000,0xffffff00,0xfffffff0],[inputA,inputB,inputC,0xff0000ff,inputD,inputE],[inputA,inputB,inputC,0xff0000ff,inputD,0xffffff00],[inputA,inputB,inputC,0xff008800,inputD,inputE],[inputA,inputB,inputC,0xff00aa00,inputD,inputE],[inputA,inputB,inputC,0xff00cc00,inputD,inputE],[inputA,inputB,inputC,0xff00ee00,inputD,inputE],[inputA,inputB,inputC,0xff00ee00,inputE,0xffffeeee],[inputA,inputB,inputC,0xff00f000,inputD,inputE],[inputA,inputB,inputC,inputD,0xff00ff0f,inputE],[inputA,inputB,inputC,inputD,0xff00ff88,inputE],[inputA,inputB,inputC,inputD,0xff00ffaa,inputE],[inputA,inputB,inputC,inputD,0xff00ffcc,inputE],[inputA,inputB,inputC,inputD,0xff00ffee,inputE],[inputA,inputB,inputC,inputD,0xff00ffff,inputE],[inputA,inputB,inputC,inputD,0xff0fffff,inputE],[inputA,inputB,inputC,inputD,0xff55ffff,inputE],[inputA,inputB,inputC,inputD,0xff80ff80,inputE],[inputA,inputB,inputC,inputD,0xff88ff00,inputE],[inputA,inputB,inputC,inputD,0xff88ff88,inputE],[inputA,inputB,inputC,inputD,0xff88ffaa,inputE],[inputA,inputB,inputC,inputD,0xff88ffff,inputE],[inputA,inputB,inputC,inputD,0xffa0ffa0,inputE],[inputA,inputB,inputC,inputD,0xffa8ffa8,inputE],[inputA,inputB,inputC,inputD,0xffaa0000,inputE],[inputA,inputB,inputC,inputD,0xffaaaaaa,inputE],[inputA,inputB,inputC,inputD,0xffaaff00,inputE],[inputA,inputB,inputC,inputD,0xffaaff88,inputE],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,inputD,0xffaaffee,inputE],[inputA,inputB,inputC,inputD,0xffaaffff,inputE],[inputA,inputB,inputC,inputD,0xffbbffbb,inputE],[inputA,inputB,inputC,inputD,0xffc0ffc0,inputE],[inputA,inputB,inputC,inputD,0xffcccccc,inputE],[inputA,inputB,inputC,inputD,0xffccff00,inputE],[inputA,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,inputD,0xffccffee,inputE],[inputA,inputB,inputC,inputD,0xffccffff,inputE],[inputA,inputB,inputC,inputD,0xffeaffea,inputE],[inputA,inputB,inputC,inputD,0xffeeeeee,inputE],[inputA,inputB,inputC,inputD,0xffeeff00,inputE],[inputA,inputB,inputC,inputD,0xffeeffaa,inputE],[inputA,inputB,inputC,inputD,0xffeeffee,inputE],[inputA,inputB,inputC,inputD,0xffeeffff,inputE],[inputA,inputB,inputC,inputD,0xfff00000,inputE],[inputA,inputB,inputC,inputD,0xfff00000,0xfffff0f0],[inputA,inputB,inputC,inputD,0xfff00000,0xffffff00],[inputA,inputB,inputC,inputD,0xfff0f0f0,inputE],[inputA,inputB,inputC,inputD,0xfff0ff00,inputE],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,inputD,0xfff0ffff,inputE],[inputA,inputB,inputC,inputD,0xfff3fff3,inputE],[inputA,inputB,inputC,inputD,0xfff7fff7,inputE],[inputA,inputB,inputC,inputD,0xfff8fff8,inputE],[inputA,inputB,inputC,inputD,0xfffaaaaa,inputE],[inputA,inputB,inputC,inputD,0xfffafafa,inputE],[inputA,inputB,inputC,inputD,0xfffafffa,inputE],[inputA,inputB,inputC,inputD,0xfffccccc,inputE],[inputA,inputB,inputC,inputD,0xfffcfffc,inputE],[inputA,inputB,inputC,inputD,0xfffefffe,inputE],[inputA,inputB,inputC,inputD,inputE,0xffff000f],[inputA,inputB,inputC,inputD,inputE,0xffff00aa],[inputA,inputB,inputC,inputD,inputE,0xffff00ff],[inputA,inputB,inputC,inputD,inputE,0xffff0fff],[inputA,inputB,inputC,inputD,inputE,0xffff8080],[inputA,inputB,inputC,inputD,inputE,0xffff8888],[inputA,inputB,inputC,inputD,inputE,0xffffa0a0],[inputA,inputB,inputC,inputD,inputE,0xffffa8a8],[inputA,inputB,inputC,inputD,inputE,0xffffaa00],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,inputE,0xffffaaff],[inputA,inputB,inputC,inputD,inputE,0xffffbbbb],[inputA,inputB,inputC,inputD,inputE,0xffffc0c0],[inputA,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xffffeaea],[inputA,inputB,inputC,inputD,inputE,0xffffeeee],[inputA,inputB,inputC,inputD,inputE,0xfffff000],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xfffff3f3],[inputA,inputB,inputC,inputD,inputE,0xfffff7f7],[inputA,inputB,inputC,inputD,inputE,0xfffff8f8],[inputA,inputB,inputC,inputD,inputE,0xfffffaaa],[inputA,inputB,inputC,inputD,inputE,0xfffffafa],[inputA,inputB,inputC,inputD,inputE,0xfffffccc],[inputA,inputB,inputC,inputD,inputE,0xfffffcfc],[inputA,inputB,inputC,inputD,inputE,0xfffffefe],[inputA,inputB,inputC,inputD,inputE,0xffffff00],[inputA,inputB,inputC,inputD,inputE,0xffffff88],[inputA,inputB,inputC,inputD,inputE,0xffffffaa],[inputA,inputB,inputC,inputD,inputE,0xffffffcc],[inputA,inputB,inputC,inputD,inputE,0xffffffee],[inputA,inputB,inputC,inputD,inputE,0xfffffff0],[inputA,inputB,inputC,inputD,inputE,0xfffffffa],[inputA,inputB,inputC,inputD,inputE,0xfffffffc],[inputA,inputB,inputC,inputD,0xffff000f,0xfffffff0],[inputA,inputB,inputC,inputD,0xffff00aa,0xffffff00],[inputA,inputB,inputC,inputD,0xffff00ff,0xffffff00],[inputA,inputB,inputC,inputD,0xffff0fff,0xfffff000],[inputA,inputB,inputC,inputD,0xffff8888,0xfffff0f0],[inputA,inputB,inputC,inputD,0xffff8888,0xffffff00],[inputA,inputB,inputC,inputD,0xffffaaaa,0xfffff000],[inputA,inputB,inputC,inputD,0xffffcccc,0xfffff000],[inputA,inputB,inputC,0xff00ff0f,0xfff0fff0,inputE],[inputA,inputB,inputC,0xff00ff0f,inputE,0xfffffff0],[inputA,inputB,inputC,0xff00ffaa,inputE,0xffffff00],[inputA,inputB,inputC,0xff00ffff,inputE,0xffffff00],[inputA,inputB,inputC,0xff00ffff,0xffff00ff,0xffffff00],[inputA,inputB,inputC,0xff88ff88,0xfff0fff0,inputE],[inputA,inputB,0xf0f0f0ff,inputD,0xfff0fff0,inputE],[inputA,inputB,0xf0f0f0ff,inputD,inputE,0xfffffff0],[inputA,inputB,0xf0f0ffff,inputD,inputE,0xfffff0f0],[inputA,inputB,0xf3f3f3f3,0xf8f8f8f8,inputD,inputE],[inputA,inputB,0xf3f3f3f3,0xfcfcfcfc,inputD,inputE],[inputA,inputB,0xf7f7f7f7,0xf8f8f8f8,inputD,inputE],[inputA,inputB,0xf8f8f8f8,inputD,0xfff0fff0,inputE],[inputA,inputB,0xf8f8f8f8,inputD,inputE,0xfffff0f0],[inputA,0xcccccccf,inputC,inputD,0xfff0fff0,inputE],[inputA,0xcccccccf,inputC,inputD,inputE,0xfffffff0],[inputA,0xcccceeee,inputC,inputD,inputE,0xffffcccc],[inputA,0xccccffff,inputC,inputD,inputE,0xffffcccc],[inputA,0xf0000000,inputC,0xfccccccc,inputD,inputE],[0xaaaaaaaf,inputB,inputC,inputD,0xfff0fff0,inputE],[0xaaaaaaaf,inputB,inputC,inputD,inputE,0xfffffff0],[0xaaaaaaff,inputB,inputC,inputD,0xffaaffaa,inputE],[0xaaaaaaff,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaaaaff,inputB,inputC,inputD,inputE,0xffffffaa],[0xaaaaeeee,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaaffff,inputB,0xeeeeaaaa,inputC,inputD,inputE],[0xaaaaffff,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaffffff,inputB,inputC,inputD,0xffaaaaaa,inputE],[0xbbbbbbbb,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputB,0xeaeaeaea,inputC,inputD,0xffaaffaa,inputE],[inputB,0xeaeaeaea,inputC,inputD,inputE,0xffffaaaa],[inputB,0xeeeeaaaa,inputC,0xfafafafa,inputD,inputE],[inputB,0xeeeeaaaa,inputC,inputD,0xffaaffaa,inputE],[inputB,0xeeeeeeee,inputC,inputD,0xffaaaaaa,inputE],[inputB,0xf0000000,inputC,0xfaaaaaaa,inputD,inputE],[inputB,inputC,0xfafafafa,inputD,0xffaaaaaa,inputE]]
def x5s5d0rg0c : List (ℕ × ℕ) := [(1,0),(1,24),(2,0),(2,24),(3,0),(4,0),(5,0),(5,24),(7,0),(7,6),(8,0),(9,0),(10,0),(11,0),(9,24),(10,24)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg0 : ∀ q (hq : q < x5s5d0r.size), 0 ≤ q → q < 16 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 0 x5s5d0rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg16c : List (ℕ × ℕ) := [(12,0),(9,30),(10,30),(13,0),(14,0),(15,24),(15,30),(16,0),(17,0),(18,0),(20,0),(20,24),(10,32),(21,0),(22,0),(24,32)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg16 : ∀ q (hq : q < x5s5d0r.size), 16 ≤ q → q < 32 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 16 x5s5d0rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg32c : List (ℕ × ℕ) := [(25,0),(25,2),(26,0),(27,0),(28,0),(27,6),(29,0),(27,8),(30,0),(31,0),(32,0),(33,0),(34,0),(35,0),(36,0),(37,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg32 : ∀ q (hq : q < x5s5d0r.size), 32 ≤ q → q < 48 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 32 x5s5d0rg32c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg48c : List (ℕ × ℕ) := [(38,0),(39,0),(40,0),(27,48),(27,50),(36,24),(32,24),(37,24),(38,24),(29,30),(41,0),(29,32),(42,0),(43,0),(27,60),(35,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg48 : ∀ q (hq : q < x5s5d0r.size), 48 ≤ q → q < 64 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 48 x5s5d0rg48c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg64c : List (ℕ × ℕ) := [(36,30),(37,30),(44,0),(35,32),(36,32),(32,32),(33,32),(37,32),(39,32),(43,60),(45,0),(45,6),(46,0),(47,0),(45,60),(48,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg64 : ∀ q (hq : q < x5s5d0r.size), 64 ≤ q → q < 80 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 64 x5s5d0rg64c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg80c : List (ℕ × ℕ) := [(46,32),(49,0),(47,32),(48,32),(50,0),(51,0),(52,0),(53,0),(53,2),(52,72),(0,33),(2,9),(56,0),(56,24),(8,33),(10,33)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg80 : ∀ q (hq : q < x5s5d0r.size), 80 ≤ q → q < 96 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 80 x5s5d0rg80c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg96c : List (ℕ × ℕ) := [(13,3),(16,3),(58,0),(59,0),(62,0),(62,6),(27,9),(63,0),(64,0),(64,1),(65,0),(66,0),(67,0),(68,0),(68,6),(69,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg96 : ∀ q (hq : q < x5s5d0r.size), 96 ≤ q → q < 112 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 96 x5s5d0rg96c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg112c : List (ℕ × ℕ) := [(65,24),(66,24),(68,24),(70,0),(63,30),(64,30),(65,30),(66,30),(32,33),(37,33),(45,1),(45,7),(48,1),(50,1),(52,1),(53,73)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg112 : ∀ q (hq : q < x5s5d0r.size), 112 ≤ q → q < 128 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 112 x5s5d0rg112c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg128c : List (ℕ × ℕ) := [(71,0),(72,0),(73,0),(74,0),(75,0),(76,0),(77,0),(78,0),(79,0),(79,6),(3,64),(4,64),(6,93),(15,16),(14,76),(16,76)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg128 : ∀ q (hq : q < x5s5d0r.size), 128 ≤ q → q < 144 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 128 x5s5d0rg128c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg144c : List (ℕ × ℕ) := [(21,64),(81,0),(82,0),(83,0),(84,0),(81,24),(82,24),(83,24),(84,24),(63,32),(64,32),(66,32),(45,4),(48,4),(50,4),(53,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg144 : ∀ q (hq : q < x5s5d0r.size), 144 ≤ q → q < 160 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 144 x5s5d0rg144c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg160c : List (ℕ × ℕ) := [(53,76),(63,33),(66,33),(77,3),(85,0),(86,0),(87,0),(87,24),(16,90),(18,90),(19,117),(57,45),(22,112),(60,41),(23,105),(24,105)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg160 : ∀ q (hq : q < x5s5d0r.size), 160 ≤ q → q < 176 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 160 x5s5d0rg160c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg176c : List (ℕ × ℕ) := [(58,64),(45,18),(48,18),(45,66),(50,18),(53,18),(53,90),(66,72),(66,78),(66,80),(37,105),(47,96),(49,96),(45,108),(50,96),(53,96)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg176 : ∀ q (hq : q < x5s5d0r.size), 176 ≤ q → q < 192 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 176 x5s5d0rg176c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg192c : List (ℕ × ℕ) := [(51,96),(77,72),(78,72),(54,105),(55,105),(59,112),(61,117),(77,76),(77,90),(76,90),(75,90),(78,90),(79,90),(80,93),(85,64),(86,64)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg192 : ∀ q (hq : q < x5s5d0r.size), 192 ≤ q → q < 208 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 192 x5s5d0rg192c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg208c : List (ℕ × ℕ) := [(87,64),(88,33),(89,0),(89,1),(90,0),(91,0),(92,0),(92,1),(93,0),(94,0),(94,6),(95,30),(96,0),(89,4),(90,2),(91,2)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg208 : ∀ q (hq : q < x5s5d0r.size), 208 ≤ q → q < 224 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 208 x5s5d0rg208c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg224c : List (ℕ × ℕ) := [(94,8),(95,32),(97,0),(90,3),(90,9),(91,3),(92,3),(92,5),(97,4),(98,0),(100,0),(100,6),(101,0),(100,8),(102,0),(100,3)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg224 : ∀ q (hq : q < x5s5d0r.size), 224 ≤ q → q < 240 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 224 x5s5d0rg224c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg240c : List (ℕ × ℕ) := [(100,9),(102,4),(101,24),(102,24),(103,0),(103,4),(104,0),(105,0),(105,1),(106,0),(107,0),(108,0),(109,0),(106,24),(107,24),(110,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg240 : ∀ q (hq : q < x5s5d0r.size), 240 ≤ q → q < 256 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 240 x5s5d0rg240c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg256c : List (ℕ × ℕ) := [(111,0),(100,48),(100,50),(100,51),(108,24),(108,27),(109,24),(112,0),(112,2),(112,3),(113,0),(103,60),(103,61),(114,0),(116,0),(117,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg256 : ∀ q (hq : q < x5s5d0r.size), 256 ≤ q → q < 272 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 256 x5s5d0rg256c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg272c : List (ℕ × ℕ) := [(118,0),(119,0),(119,24),(120,0),(103,64),(114,2),(118,2),(119,2),(119,26),(120,2),(121,0),(118,3),(119,3),(119,27),(120,3),(121,1)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg272 : ∀ q (hq : q < x5s5d0r.size), 272 ≤ q → q < 288 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 272 x5s5d0rg272c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg288c : List (ℕ × ℕ) := [(121,4),(122,24),(123,0),(101,9),(125,0),(126,0),(127,0),(128,0),(125,24),(126,24),(127,24),(128,24),(131,0),(132,24),(133,0),(89,18)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg288 : ∀ q (hq : q < x5s5d0r.size), 288 ≤ q → q < 304 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 288 x5s5d0rg288c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg304c : List (ℕ × ℕ) := [(91,12),(90,15),(91,13),(97,7),(97,18),(100,13),(102,7),(102,18),(103,18),(104,6),(108,6),(109,6),(106,30),(108,30),(119,6),(109,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg304 : ∀ q (hq : q < x5s5d0r.size), 304 ≤ q → q < 320 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 304 x5s5d0rg304c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg320c : List (ℕ × ℕ) := [(122,30),(125,6),(124,30),(125,30),(132,30),(125,18),(97,8),(136,0),(97,9),(102,8),(102,9),(112,48),(137,0),(138,0),(139,0),(139,6)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg320 : ∀ q (hq : q < x5s5d0r.size), 320 ≤ q → q < 336 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 320 x5s5d0rg320c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg336c : List (ℕ × ℕ) := [(140,0),(142,0),(143,0),(90,17),(90,64),(91,16),(92,16),(92,22),(97,10),(100,16),(102,10),(100,40),(104,8),(109,8),(108,40),(109,32)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg336 : ∀ q (hq : q < x5s5d0r.size), 336 ≤ q → q < 352 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 336 x5s5d0rg336c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg352c : List (ℕ × ℕ) := [(125,8),(129,8),(124,32),(125,32),(97,21),(137,12),(144,0),(145,0),(146,0),(102,45),(104,9),(108,9),(109,9),(111,9),(103,49),(103,52)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg352 : ∀ q (hq : q < x5s5d0r.size), 352 ≤ q → q < 368 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 352 x5s5d0rg352c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg368c : List (ℕ × ℕ) := [(100,57),(112,9),(116,9),(108,33),(118,9),(119,9),(103,66),(100,63),(112,15),(116,15),(118,15),(119,15),(121,9),(100,65),(112,17),(116,17)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg368 : ∀ q (hq : q < x5s5d0r.size), 368 ≤ q → q < 384 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 368 x5s5d0rg368c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg384c : List (ℕ × ℕ) := [(108,41),(118,17),(119,17),(121,11),(121,21),(109,33),(119,33),(120,9),(119,39),(120,15),(119,41),(120,17),(137,3),(139,3),(139,9),(136,21)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg384 : ∀ q (hq : q < x5s5d0r.size), 384 ≤ q → q < 400 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 384 x5s5d0rg384c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg400c : List (ℕ × ℕ) := [(112,64),(137,16),(139,16),(139,17),(144,18),(146,18),(147,0),(115,64),(149,0),(150,0),(151,0),(153,0),(114,48),(116,51),(155,0),(156,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg400 : ∀ q (hq : q < x5s5d0r.size), 400 ≤ q → q < 416 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 400 x5s5d0rg400c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg416c : List (ℕ × ℕ) := [(125,33),(117,64),(158,0),(159,0),(125,42),(125,44),(125,45),(155,18),(89,96),(91,72),(91,73),(103,96),(104,48),(108,48),(109,48),(109,54)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg416 : ∀ q (hq : q < x5s5d0r.size), 416 ≤ q → q < 432 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 416 x5s5d0rg416c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg432c : List (ℕ × ℕ) := [(125,48),(124,54),(130,48),(125,54),(125,96),(137,24),(139,24),(90,88),(91,76),(100,82),(104,50),(125,50),(124,56),(125,56),(136,28),(137,26)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg432 : ∀ q (hq : q < x5s5d0r.size), 432 ≤ q → q < 448 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 432 x5s5d0rg432c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg448c : List (ℕ × ℕ) := [(97,99),(137,72),(102,105),(104,51),(108,51),(109,51),(109,57),(137,27),(151,24),(136,99),(112,88),(137,76),(144,28),(146,28),(144,96),(146,96)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg448 : ∀ q (hq : q < x5s5d0r.size), 448 ≤ q → q < 464 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 448 x5s5d0rg448c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg464c : List (ℕ × ℕ) := [(147,24),(148,24),(115,88),(149,24),(150,24),(153,24),(155,24),(156,24),(157,24),(117,88),(158,24),(159,24),(158,72),(97,61),(136,31),(137,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg464 : ∀ q (hq : q < x5s5d0r.size), 464 ≤ q → q < 480 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 464 x5s5d0rg464c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg480c : List (ℕ × ℕ) := [(139,30),(140,30),(141,30),(136,32),(160,0),(161,0),(136,33),(162,0),(164,0),(162,24),(97,64),(136,34),(137,32),(141,32),(160,28),(162,26)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg480 : ∀ q (hq : q < x5s5d0r.size), 480 ≤ q → q < 496 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 480 x5s5d0rg480c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg496c : List (ℕ × ℕ) := [(165,0),(166,0),(102,63),(102,65),(137,33),(139,33),(139,57),(162,3),(162,27),(166,28),(121,60),(145,32),(145,33),(121,64),(167,0),(169,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg496 : ∀ q (hq : q < x5s5d0r.size), 496 ≤ q → q < 512 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 496 x5s5d0rg496c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg512c : List (ℕ × ℕ) := [(171,0),(172,0),(90,94),(91,90),(100,92),(104,60),(109,60),(109,62),(125,60),(125,62),(131,60),(136,42),(137,36),(104,61),(108,91),(136,61)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg512 : ∀ q (hq : q < x5s5d0r.size), 512 ≤ q → q < 528 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 512 x5s5d0rg512c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg528c : List (ℕ × ℕ) := [(137,37),(137,79),(144,31),(146,31),(112,94),(137,90),(144,42),(146,42),(148,30),(115,94),(149,30),(152,30),(153,30),(153,54),(154,30),(155,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg528 : ∀ q (hq : q < x5s5d0r.size), 528 ≤ q → q < 544 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 528 x5s5d0rg528c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg544c : List (ℕ × ℕ) := [(157,30),(117,94),(158,30),(125,68),(125,69),(155,42),(158,78),(132,92),(132,93),(158,90),(136,62),(161,12),(136,63),(160,31),(162,30),(163,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg544 : ∀ q (hq : q < x5s5d0r.size), 544 ≤ q → q < 560 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 544 x5s5d0rg544c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg560c : List (ℕ × ℕ) := [(164,30),(137,38),(160,18),(162,12),(160,42),(162,36),(137,39),(162,37),(166,31),(166,42),(121,70),(167,6),(169,6),(170,6),(171,6),(172,6)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg560 : ∀ q (hq : q < x5s5d0r.size), 560 ≤ q → q < 576 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 560 x5s5d0rg560c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg576c : List (ℕ × ℕ) := [(171,18),(137,80),(160,96),(162,72),(137,81),(162,79),(121,112),(167,48),(170,48),(171,48),(146,32),(144,32),(173,0),(146,33),(144,33),(166,61)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg576 : ∀ q (hq : q < x5s5d0r.size), 576 ≤ q → q < 592 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 576 x5s5d0rg576c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg592c : List (ℕ × ℕ) := [(173,7),(174,0),(176,0),(99,64),(104,64),(108,94),(109,64),(111,64),(118,64),(119,64),(118,88),(119,88),(118,94),(119,94),(109,65),(111,65)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg592 : ∀ q (hq : q < x5s5d0r.size), 592 ≤ q → q < 608 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 592 x5s5d0rg592c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg608c : List (ℕ × ℕ) := [(120,64),(120,88),(120,94),(134,64),(135,64),(136,64),(137,40),(137,82),(144,34),(146,34),(137,92),(149,32),(152,32),(153,32),(153,56),(154,32)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg608 : ∀ q (hq : q < x5s5d0r.size), 608 ≤ q → q < 624 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 608 x5s5d0rg608c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg624c : List (ℕ × ℕ) := [(155,32),(158,32),(158,80),(160,32),(160,34),(162,32),(163,32),(164,32),(162,38),(166,32),(137,41),(162,16),(162,40),(166,34),(167,8),(170,8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg624 : ∀ q (hq : q < x5s5d0r.size), 624 ≤ q → q < 640 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 624 x5s5d0rg624c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg640c : List (ℕ × ℕ) := [(171,8),(171,20),(162,80),(162,76),(162,82),(167,50),(170,50),(171,50),(173,8),(173,4),(166,64),(173,10),(174,2),(176,2),(137,93),(139,93)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg640 : ∀ q (hq : q < x5s5d0r.size), 640 ≤ q → q < 656 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 640 x5s5d0rg640c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg656c : List (ℕ × ℕ) := [(139,95),(162,90),(162,92),(167,60),(171,60),(171,66),(172,90),(173,60),(166,21),(173,18),(174,12),(166,99),(174,72),(177,0),(149,33),(153,33)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg656 : ∀ q (hq : q < x5s5d0r.size), 656 ≤ q → q < 672 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 656 x5s5d0rg656c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg672c : List (ℕ × ℕ) := [(155,33),(158,33),(160,33),(162,33),(162,39),(166,33),(162,41),(167,9),(171,9),(171,21),(162,81),(167,51),(173,9),(174,3),(162,93),(167,61)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg672 : ∀ q (hq : q < x5s5d0r.size), 672 ≤ q → q < 688 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 672 x5s5d0rg672c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg688c : List (ℕ × ℕ) := [(171,67),(172,91),(173,61),(173,21),(174,13),(173,99),(174,73),(177,1),(167,64),(173,64),(174,16),(174,76),(177,4),(174,90),(177,18),(177,96)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg688 : ∀ q (hq : q < x5s5d0r.size), 688 ≤ q → q < 704 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 688 x5s5d0rg688c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg704c : List (ℕ × ℕ) := [(179,0),(180,0),(182,0),(183,0),(184,0),(184,2),(184,60),(184,84),(178,1),(179,1),(180,1),(182,1),(185,0),(184,1),(178,4),(179,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg704 : ∀ q (hq : q < x5s5d0r.size), 704 ≤ q → q < 720 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 704 x5s5d0rg704c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg720c : List (ℕ × ℕ) := [(182,4),(181,16),(182,16),(183,64),(184,4),(184,5),(168,66),(175,90),(180,18),(182,18),(92,90),(168,108),(175,114),(178,96),(178,97),(179,96)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg720 : ∀ q (hq : q < x5s5d0r.size), 720 ≤ q → q < 736 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 720 x5s5d0rg720c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
def x5s5d0rg736c : List (ℕ × ℕ) := [(180,96),(181,96),(182,96),(183,96),(182,114),(184,96),(184,97),(184,99),(184,101),(184,112),(92,114),(184,118)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rg736 : ∀ q (hq : q < x5s5d0r.size), 736 ≤ q → q < 748 → ¬ Reach x5s5d0r[q].toFinset 5 0 0xfee8e880 := by
  have check : aliasPart x5s5d0r x5s5d0 0xfee8e880 x5maps 736 x5s5d0rg736c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d0rok : correct x5s5d0r 5 0 0xfee8e880 := by
  intro q hq
  have lim : q < 748 := hq
  by_cases atMid : q < 368
  ·
    by_cases atMid : q < 176
    ·
      by_cases atMid : q < 80
      ·
        by_cases atMid : q < 32
        ·
          by_cases atMid : q < 16
          ·
            exact x5s5d0rg0 q hq (by omega) (by omega)
          ·
            exact x5s5d0rg16 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 48
          ·
            exact x5s5d0rg32 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 64
            ·
              exact x5s5d0rg48 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg64 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 128
        ·
          by_cases atMid : q < 96
          ·
            exact x5s5d0rg80 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 112
            ·
              exact x5s5d0rg96 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg112 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 144
          ·
            exact x5s5d0rg128 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 160
            ·
              exact x5s5d0rg144 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg160 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 272
      ·
        by_cases atMid : q < 224
        ·
          by_cases atMid : q < 192
          ·
            exact x5s5d0rg176 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 208
            ·
              exact x5s5d0rg192 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg208 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 240
          ·
            exact x5s5d0rg224 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 256
            ·
              exact x5s5d0rg240 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg256 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 320
        ·
          by_cases atMid : q < 288
          ·
            exact x5s5d0rg272 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 304
            ·
              exact x5s5d0rg288 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg304 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 336
          ·
            exact x5s5d0rg320 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 352
            ·
              exact x5s5d0rg336 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg352 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 560
    ·
      by_cases atMid : q < 464
      ·
        by_cases atMid : q < 416
        ·
          by_cases atMid : q < 384
          ·
            exact x5s5d0rg368 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 400
            ·
              exact x5s5d0rg384 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg400 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 432
          ·
            exact x5s5d0rg416 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 448
            ·
              exact x5s5d0rg432 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg448 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 512
        ·
          by_cases atMid : q < 480
          ·
            exact x5s5d0rg464 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 496
            ·
              exact x5s5d0rg480 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg496 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 528
          ·
            exact x5s5d0rg512 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 544
            ·
              exact x5s5d0rg528 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg544 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 656
      ·
        by_cases atMid : q < 608
        ·
          by_cases atMid : q < 576
          ·
            exact x5s5d0rg560 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 592
            ·
              exact x5s5d0rg576 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg592 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 624
          ·
            exact x5s5d0rg608 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 640
            ·
              exact x5s5d0rg624 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg640 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 704
        ·
          by_cases atMid : q < 672
          ·
            exact x5s5d0rg656 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 688
            ·
              exact x5s5d0rg672 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg688 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 720
          ·
            exact x5s5d0rg704 q hq (by omega) (by omega)
          ·
            by_cases atMid : q < 736
            ·
              exact x5s5d0rg720 q hq (by omega) (by omega)
            ·
              exact x5s5d0rg736 q hq (by omega) (by omega)
def x5s5d1 : Array (List Word) := #[[0x80008000,inputA,inputB,inputC,inputD,inputE],[0x80808080,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,0xffff8080],[0x80808080,inputA,inputB,0xf8f8f8f8,inputD,inputE],[0x88808880,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x88888888,0xaaa0aaa0,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffff8080],[0x88888888,inputA,0xecececec,inputC,inputD,inputE],[0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xe0e0e0e0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE],[0xa888a888,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfefefefe,inputD,inputE],[0xaaa8aaa8,inputA,inputB,inputC,inputD,inputE],[0xaaa8aaa8,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xaaa8aaa8,inputB,inputC,inputD,0xfffcfffc,inputE],[inputA,inputB,0xeaaaeaaa,inputC,inputD,inputE],[inputA,inputB,0xeac0eac0,inputC,inputD,inputE],[inputA,inputB,0xeaeaeaea,inputC,inputD,inputE],[inputA,inputB,0xeee0eee0,inputC,inputD,inputE],[inputA,inputB,0xeeeaeeea,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,inputC,0xfeeefeee,inputD,inputE],[inputA,inputB,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,inputC,inputD,0xfffefffe,inputE],[inputA,inputB,inputC,inputD,0xffff8888,0xfffff0f0]]
def x5s5d1g0c : List (List ℕ × List ℕ) := [([0x21,0x11021,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x688d2,0x5f0d2,0x5a0d2,0x4f0d2,0x3e8d2,0x2a0d2]),([8,0x5008,8,0x4808,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8],[0x670d4,0x640d4,0x540d4,0x4e0d4,0x3d0d4,0x250d4]),([0x21,0x12821,0x21,0x11821,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x678d5,0x5f0d5,0x5a0d5,0x4f0d5,0x3e8d5,0x2a0d5]),([0x23,0x13023,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23],[0x680d6,0x5f8d6,0x5a8d6,0x4f8d6,0x3f0d6,0xf8d6])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g0 : ∀ q (hq : q < x5s5d1.size), 0 ≤ q → q < 4 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 0 x5s5d1g0c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g4c : List (List ℕ × List ℕ) := [([0,0x2a,0,0x29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0xd8,0xd8,0xd8,0xd8,0xd8,0xd8]),([0x21,0x14021,0x21,0x12821,0x21,0x12021,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x668e2,0x5f0e2,0x5a0e2,0x4f0e2,0x3e8e2,0x2a0e2]),([11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],[0x648ea,0x638ea,0x588ea,0x478ea,0x3d8ea,0x258ea]),([0,21,0,17,0,16,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0xee,0xee,0xee,0xee,0xee,0xee])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g4 : ∀ q (hq : q < x5s5d1.size), 4 ≤ q → q < 8 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 4 x5s5d1g4c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g8c : List (List ℕ × List ℕ) := [([26,0x1381a,26,26,26,26,0x281a,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26,26],[0x650f4,0x5e8f4,0x598f4,0x518f4,0x308f4,0x270f4]),([0x21,0x21,0x21,0x21,0x21,0x21,0x4021,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x658f6,0x5f0f6,0x5a0f6,0x4f0f6,0x3e8f6,0x2a0f6]),([0x23,0x14823,0x23,0x23,0x23,0x23,0x4823,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23,0x23],[0x660f7,0x5f8f7,0x5a8f7,0x4f8f7,0x3f0f7,0xf8f7]),([0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0xfb,0xfb,0xfb,0xfb,0xfb,0xfb])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g8 : ∀ q (hq : q < x5s5d1.size), 8 ≤ q → q < 12 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 8 x5s5d1g8c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g12c : List (List ℕ × List ℕ) := [([8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8],[0x640fc,0x5d8fc,0x540fc,0x4e0fc,0x3d0fc,0x250fc]),([8,8,8,8,8,8,8,8,8,8,8,0x808,8,8,8,8,8,8,8,8,8,8],[0x64107,0x58107,0x54107,0x4e107,0x3d107,0x25107]),([8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8],[0x64110,0x54110,0x4e110,0x48110,0x3d110,0x25110]),([8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8],[0x64111,0x54111,0x4e111,0x47111,0x3d111,0x25111])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g12 : ∀ q (hq : q < x5s5d1.size), 12 ≤ q → q < 16 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 12 x5s5d1g12c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g16c : List (List ℕ × List ℕ) := [([8,8,8,8,8,8,0x808,8,8,8,8,8,8,8,8,0x3008,8,0x3808,8,8,8],[0x64113,0x54113,0x4e113,0x45113,0x3d113,0x25113]),([8,8,8,8,8,8,8,8,8,8,8,8,0x1008,8,8,8,0x2808,8,8,8,8,8,8],[0x6411a,0x5411a,0x4e11a,0x3d11a,0x3011a,0x2511a]),([0x21,0x16021,0x21,0x21,0x21,0x21,0x21,0x21,0x6021,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x63147,0x5f147,0x5a147,0x4f147,0x3e947,0x2a147]),([0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x6294c,0x5f14c,0x5a14c,0x4f14c,0x3e94c,0x2a14c])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g16 : ∀ q (hq : q < x5s5d1.size), 16 ≤ q → q < 20 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 16 x5s5d1g16c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g20c : List (List ℕ × List ℕ) := [([8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0x14e,0x14e,0x14e,0x14e,0x14e,0x14e]),([0,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,14,0,15,0,0,0],[0x150,0x150,0x150,0x150,0x150,0x150]),([0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821,0xa821],[0x30c62166,0x2f05f166,0x2c85a166,0x2744f166,0x1f03e966,0x1302a166]),([21,21,21,21,21,21,21,21,21,21,0x9015,21,21,21,21,21,21,21,21,0x9815,21,21,21,21,21],[0x61967,0x59167,0x4e967,0x46967,0x3e167,0x26167])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g20 : ∀ q (hq : q < x5s5d1.size), 20 ≤ q → q < 24 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 20 x5s5d1g20c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g24c : List (List ℕ × List ℕ) := [([21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,0xa015,21],[0x61968,0x59168,0x4e968,0x3e168,0x2d968,0x26168]),([0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d,0x1082d],[0x2f8601e4,0x2d05b1e4,0x2b8579e4,0x278501e4,0x1f43f9e4,0x1502c9e4]),([0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x17021,0x21,0x21,0x21,0x21,0x21,0x15821,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x5f1e5,0x5a1e5,0x569e5,0x4f1e5,0x3e9e5,0x2a1e5]),([0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x5f1e7,0x5a1e7,0x561e7,0x4f1e7,0x3e9e7,0x2a1e7])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g24 : ∀ q (hq : q < x5s5d1.size), 24 ≤ q → q < 28 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 24 x5s5d1g24c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g28c : List (List ℕ × List ℕ) := [([0x1021,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0xc821,0x21,0x21,0x21,0x21,0x21],[0x5f1f0,0x5a1f0,0x559f0,0x4f1f0,0x3e9f0,0x2a1f0]),([0x1821,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0xb821,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x5f1f1,0x5a1f1,0x551f1,0x4f1f1,0x3e9f1,0x2a1f1]),([0x4021,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21],[0x5f1fe,0x5a1fe,0x549fe,0x4f1fe,0x3e9fe,0x2a1fe]),([0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0xd821,0x21,0x21,0x21,0x21,0x21,0xe821,0x21,0xf021,0x21,0x21,0x21],[0x5f24c,0x5a24c,0x4f24c,0x4624c,0x3ea4c,0x2a24c])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g28 : ∀ q (hq : q < x5s5d1.size), 28 ≤ q → q < 32 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 28 x5s5d1g28c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
def x5s5d1g32c : List (List ℕ × List ℕ) := [([0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0xe821,0x21,0xf821,0x21,0x21,0x21],[0x5f251,0x5a251,0x4f251,0x45a51,0x3ea51,0x2a251]),([0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x21,0x10021,0x21],[0x5f29d,0x5a29d,0x4f29d,0x3ea9d,0x2d29d,0x2a29d]),([0,0,0,0,0,0,0,0,22,0,0,0,0,0,0,0,24,0,0,0,28,0,0,0,0,0,0x23],[0x2c4,0x2c4,0x2c4,0x2c4,0x2c4,0x2c4])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1g32 : ∀ q (hq : q < x5s5d1.size), 32 ≤ q → q < 35 → ¬ Reach x5s5d1[q].toFinset 5 1 0xfee8e880 := by
  have check : part x5s5d1 0xfee8e880 5 1 x5s4d1r x5s5d0r 32 x5s5d1g32c = true := by decide +kernel
  exact part_ok x5s4d1rok x5s5d0rok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1ok : correct x5s5d1 5 1 0xfee8e880 := by
  intro q hq
  have lim : q < 35 := hq
  by_cases atMid : q < 16
  ·
    by_cases atMid : q < 8
    ·
      by_cases atMid : q < 4
      ·
        exact x5s5d1g0 q hq (by omega) (by omega)
      ·
        exact x5s5d1g4 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 12
      ·
        exact x5s5d1g8 q hq (by omega) (by omega)
      ·
        exact x5s5d1g12 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 24
    ·
      by_cases atMid : q < 20
      ·
        exact x5s5d1g16 q hq (by omega) (by omega)
      ·
        exact x5s5d1g20 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 28
      ·
        exact x5s5d1g24 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 32
        ·
          exact x5s5d1g28 q hq (by omega) (by omega)
        ·
          exact x5s5d1g32 q hq (by omega) (by omega)
def x5s5d1r : Array (List Word) := #[[0x80008000,inputA,inputB,inputC,inputD,inputE],[0x80800000,inputA,inputB,inputC,inputD,inputE],[0x80808080,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,inputE],[0x80808080,inputA,inputB,inputC,inputD,0xffff8080],[0x80808080,inputA,inputB,inputC,0xff80ff80,inputE],[0x80808080,inputA,inputB,0xf8f8f8f8,inputD,inputE],[0x88008800,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88008800,inputA,inputB,inputC,inputD,inputE],[0x88808880,inputA,inputB,inputC,inputD,inputE],[0x88880000,0x88888888,0xeeeeeeee,inputC,inputD,inputE],[0x88880000,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputB,0xfafafafa,inputD,inputE],[0x88888888,0xa0a0a0a0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xaa00aa00,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xaaa0aaa0,inputB,inputC,inputD,inputE],[0x88888888,0xaaaa0000,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,inputA,0xccc0ccc0,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,0xfff0fff0,inputE],[0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffff8080],[0x88888888,inputA,inputB,inputC,0xff80ff80,inputE],[0x88888888,inputA,0xecececec,inputC,inputD,inputE],[0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xc0c0c0c0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xcc00cc00,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xcccc0000,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xe0e0e0e0,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xee00ee00,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeee0000,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf000f000,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,0xf0f00000,inputC,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfcfcfcfc,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,0xff000000,inputD,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xff88ff88,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffaaffaa,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffccffcc,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xffeeffee,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffff8888],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffaaaa],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffcccc],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffeeee],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xfffff0f0],[0x88888888,0xeeeeeeee,inputC,inputD,inputE,0xffffff00],[0xa000a000,inputA,inputB,inputC,inputD,inputE],[0xa0a00000,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,0xf8f8f8f8,inputD,inputE],[0xa0a0a0a0,inputA,inputB,0xfafafafa,inputD,inputE],[0xa0a0a0a0,inputB,0xeeeeeeee,0xfafafafa,inputD,inputE],[0xa0a0a0a0,inputB,inputC,0xfafafafa,inputD,inputE],[0xa800a800,inputA,inputB,inputC,inputD,inputE],[0xa8a80000,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,0xaa00aa00,inputB,inputC,inputD,inputE],[0xa8a8a8a8,0xaaaa0000,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputA,0xc0c0c0c0,0xfcfcfcfc,inputD,inputE],[0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfafafafa,inputD,inputE],[0xa8a8a8a8,inputB,inputC,0xfefefefe,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaaa0aaa0,inputA,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[inputA,0xc000c000,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,0xf8f8f8f8,inputD,inputE],[inputA,0xc0c0c0c0,inputB,0xfcfcfcfc,inputD,inputE],[inputA,0xc0c0c0c0,inputC,0xfcfcfcfc,inputD,inputE],[inputA,0xc8c8c8c8,inputB,inputC,inputD,inputE],[inputA,0xc8c8c8c8,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xccc0ccc0,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,0xfafafafa,inputD,inputE],[inputA,inputB,0xe0e0e0e0,0xfefefefe,inputD,inputE],[inputA,inputB,0xeaeaeaea,inputC,inputD,inputE],[inputA,inputB,0xecececec,inputC,inputD,inputE],[inputA,inputB,0xee00ee00,inputC,inputD,inputE],[inputA,inputB,0xeee0eee0,inputC,inputD,inputE],[inputA,inputB,0xeeee0000,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,0xf000f000,0xfff0fff0,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfe00fe00,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfefe0000,inputD],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xf0000000,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,0xfff0fff0,inputE],[inputA,inputB,0xf000f000,inputD,0xfff0fff0,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,inputC,0xf800f800,inputD,inputE],[inputA,inputB,inputC,0xf888f888,inputD,inputE],[inputA,inputB,inputC,0xf8f80000,inputD,inputE],[inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[inputA,inputB,inputC,0xfa00fa00,inputD,inputE],[inputA,inputB,inputC,0xfaaafaaa,inputD,inputE],[inputA,inputB,inputC,0xfafa0000,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,inputC,0xfc00fc00,inputD,inputE],[inputA,inputB,inputC,0xfcccfccc,inputD,inputE],[inputA,inputB,inputC,0xfcfc0000,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,inputC,0xfe00fe00,0xfefefefe,inputE],[inputA,inputB,inputC,0xfe00fe00,inputD,inputE],[inputA,inputB,inputC,0xfefe0000,0xfefefefe,inputD],[inputA,inputB,inputC,0xfefe0000,inputD,inputE],[inputA,inputB,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,inputC,0xff000000,inputD,inputE],[inputA,inputB,inputC,inputD,0xff80ff80,inputE],[inputA,inputB,inputC,inputD,0xff88ff88,inputE],[inputA,inputB,inputC,inputD,0xffa0ffa0,inputE],[inputA,inputB,inputC,inputD,0xffa8ffa8,inputE],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,inputD,0xffeeffee,inputE],[inputA,inputB,inputC,inputD,0xfff00000,inputE],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,inputD,0xfff8fff8,inputE],[inputA,inputB,inputC,inputD,0xfffafffa,inputE],[inputA,inputB,inputC,inputD,0xfffcfffc,inputE],[inputA,inputB,inputC,inputD,0xfffefffe,inputE],[inputA,inputB,inputC,inputD,inputE,0xffff8080],[inputA,inputB,inputC,inputD,inputE,0xffff8888],[inputA,inputB,inputC,inputD,inputE,0xffffa0a0],[inputA,inputB,inputC,inputD,inputE,0xffffa8a8],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xffffeeee],[inputA,inputB,inputC,inputD,inputE,0xfffff000],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xfffff8f8],[inputA,inputB,inputC,inputD,inputE,0xfffffafa],[inputA,inputB,inputC,inputD,inputE,0xfffffcfc],[inputA,inputB,inputC,inputD,inputE,0xfffffefe],[inputA,inputB,inputC,inputD,inputE,0xffffff00],[inputA,inputB,inputC,inputD,inputE,0xfffffff0],[inputA,inputB,inputC,0xff88ff88,0xfff0fff0,inputE],[inputA,inputB,0xf8f8f8f8,inputD,0xfff0fff0,inputE],[inputA,inputB,0xf8f8f8f8,inputD,inputE,0xfffff0f0]]
def x5s5d1rg0c : List (ℕ × ℕ) := [(0,0),(0,1),(1,0),(2,0),(3,0),(3,1),(4,0),(1,2),(2,2),(5,0),(1,3),(2,3),(6,0),(6,6),(6,8),(7,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg0 : ∀ q (hq : q < x5s5d1r.size), 0 ≤ q → q < 16 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 0 x5s5d1rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg16c : List (ℕ × ℕ) := [(6,9),(7,24),(8,0),(9,0),(10,0),(10,1),(11,0),(12,0),(6,48),(6,50),(6,51),(12,24),(13,0),(13,2),(13,3),(8,60)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg16 : ∀ q (hq : q < x5s5d1r.size), 16 ≤ q → q < 32 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 16 x5s5d1rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg32c : List (ℕ × ℕ) := [(8,61),(14,0),(15,0),(15,24),(16,0),(8,64),(14,2),(15,2),(15,26),(16,2),(17,0),(14,3),(15,3),(15,27),(16,3),(17,1)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg32 : ∀ q (hq : q < x5s5d1r.size), 32 ≤ q → q < 48 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 32 x5s5d1rg32c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg48c : List (ℕ × ℕ) := [(17,4),(2,12),(2,13),(9,6),(11,6),(12,6),(15,6),(12,30),(5,8),(5,9),(7,8),(7,9),(13,48),(19,0),(20,0),(20,6)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg48 : ∀ q (hq : q < x5s5d1r.size), 48 ≤ q → q < 64 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 48 x5s5d1rg48c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg64c : List (ℕ × ℕ) := [(21,0),(9,8),(19,12),(9,9),(2,72),(9,48),(11,48),(12,48),(12,54),(19,24),(20,24),(9,50),(19,72),(9,51),(19,30),(20,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg64 : ∀ q (hq : q < x5s5d1r.size), 64 ≤ q → q < 80 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 64 x5s5d1rg64c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg80c : List (ℕ × ℕ) := [(21,30),(27,0),(27,24),(19,32),(28,0),(19,33),(17,60),(23,32),(23,33),(30,0),(2,90),(9,60),(12,60),(12,62),(9,61),(18,62)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg80 : ∀ q (hq : q < x5s5d1r.size), 80 ≤ q → q < 96 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 80 x5s5d1rg80c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg96c : List (ℕ × ℕ) := [(26,12),(18,63),(27,30),(19,38),(27,12),(19,39),(30,6),(19,80),(27,72),(19,81),(30,48),(24,32),(22,32),(24,33),(22,33),(32,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg96 : ∀ q (hq : q < x5s5d1r.size), 96 ≤ q → q < 112 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 96 x5s5d1rg96c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg112c : List (ℕ × ℕ) := [(9,64),(25,32),(27,32),(27,38),(29,32),(30,8),(30,50),(32,2),(19,93),(30,60),(31,60),(32,12),(32,72),(33,0),(25,33),(27,33)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg112 : ∀ q (hq : q < x5s5d1r.size), 112 ≤ q → q < 128 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 112 x5s5d1rg112c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
def x5s5d1rg128c : List (ℕ × ℕ) := [(27,39),(29,33),(30,9),(30,51),(32,3),(27,93),(30,61),(31,61),(32,13),(32,73),(33,1),(30,64),(32,90),(34,1),(34,4),(34,5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rg128 : ∀ q (hq : q < x5s5d1r.size), 128 ≤ q → q < 144 → ¬ Reach x5s5d1r[q].toFinset 5 1 0xfee8e880 := by
  have check : aliasPart x5s5d1r x5s5d1 0xfee8e880 x5maps 128 x5s5d1rg128c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s5d1ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s5d1rok : correct x5s5d1r 5 1 0xfee8e880 := by
  intro q hq
  have lim : q < 144 := hq
  by_cases atMid : q < 64
  ·
    by_cases atMid : q < 32
    ·
      by_cases atMid : q < 16
      ·
        exact x5s5d1rg0 q hq (by omega) (by omega)
      ·
        exact x5s5d1rg16 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 48
      ·
        exact x5s5d1rg32 q hq (by omega) (by omega)
      ·
        exact x5s5d1rg48 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 96
    ·
      by_cases atMid : q < 80
      ·
        exact x5s5d1rg64 q hq (by omega) (by omega)
      ·
        exact x5s5d1rg80 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 112
      ·
        exact x5s5d1rg96 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 128
        ·
          exact x5s5d1rg112 q hq (by omega) (by omega)
        ·
          exact x5s5d1rg128 q hq (by omega) (by omega)
def x5s6d0 : Array (List Word) := #[[15,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[15,inputA,inputB,inputC,inputD,inputE,0xfffffff0],[0xaa,0xff,inputA,inputB,inputC,inputD,inputE],[0xaa,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xff,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xff,0xaaaaaa00,inputA,inputB,inputC,inputD,inputE],[0xff,inputA,0xaaaaaaff,inputB,inputC,inputD,inputE],[0xff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xff,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xff,inputA,inputB,inputC,0xff000000,inputD,0xffffff00],[0xff,inputA,inputB,inputC,inputD,0xff00ffff,inputE],[0xff,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xff,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xff,inputA,inputB,inputC,inputD,inputE,0xffffffaa],[0xff,inputA,inputB,inputC,inputD,0xffff00ff,0xffffff00],[0xfff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xfff,inputA,inputB,inputC,inputD,inputE,0xfffff000],[0x8888,0xaaaa,inputA,inputB,inputC,inputD,inputE],[0x8888,0xffff,inputA,inputB,inputC,inputD,inputE],[0x8888,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xcccc,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xffff,0xaaaa0000,inputB,inputC,inputD,inputE],[0xaaaa,0xffff,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xffff,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa,0x5555ffff,0xaaaa0000,inputB,inputC,inputD,inputE],[0xaaaa,0x5555ffff,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xcccceeee,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xccccffff,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaaaa,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xaaaa,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaa,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0xeeee,0xffff,inputA,inputB,inputC,inputD,inputE],[0xeeee,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffff,0x80808080,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88880000,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0xffff,0x8888aaaa,inputA,inputB,inputC,inputD,inputE],[0xffff,0x8888ffff,inputA,inputB,inputC,inputD,inputE],[0xffff,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputA,inputB,inputC,inputD,0xffffaaaa],[0xffff,0xaaaa0000,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffff,0xaaaa8888,inputA,inputB,inputC,inputD,inputE],[0xffff,inputA,0xaaaaeeee,inputB,inputC,inputD,inputE],[0xffff,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeaeaeaea,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeee0000,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeeaaaa,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeeffff,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffff8888],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffeeee],[0xffff,inputA,inputB,inputC,0xff00ffff,inputE,0xffffff00],[0xfffff,inputA,inputB,inputC,inputD,0xfff00000,inputE],[0xfffff,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xaaaaaa,0xffffff,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xffffff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xffffff,0xaa000000,inputA,inputB,inputC,inputD,inputE],[0xffffff,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xffffff,inputA,0xaaffffff,inputB,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffffff,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xffffff,inputA,inputB,inputC,0xff000000,inputD,0xffffff00],[0xffffff,inputA,inputB,inputC,inputD,0xffaaaaaa,inputE],[0xffffff,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xffffff,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xfffffff,inputA,inputB,0xf0000000,inputC,inputD,inputE],[0xfffffff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x80808080,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88888888,0x8888ffff,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xbbbbbbbb,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf3f3f3f3,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf7f7f7f7,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0x8888aaaa,inputA,inputB,0xccccffff,inputC,inputD,inputE],[0xa8a8a8a8,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,0xaaaaaaff,inputB,inputC,inputD,inputE,0xffffff00],[inputA,0xaaaaffff,inputB,0xccccffff,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,0xeeeeffff,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,0xeeeeeeee,0xeeeeffff,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE]]
def x5s6d0g0c : List (List ℕ × List ℕ) := [([0x2a93,0x732cb6c02a93,0x402a93,0x63a0b5802a93,0x434b3802a93,0x4d6b2002a93,0xa5002a93,0xa7802a93,0x3d802a93,0x7f802a93,0x4e402a93,0x8ec02a93,0x57002a93,0x9f802a93,0x59402a93,0xa6802a93,0x5a802a93,0xa9c02a93,0x6b002a93,0x91c02a93,0x6e802a93,0xa1402a93,0x70402a93,0xa7002a93,0x70c02a93,0xaac02a93,0x220540c81c02a93,0x83402a93,0xabc02a93,0x95002a93,0xae002a93,0xa3802a93,0xaf402a93],[]),([0x2abd,0x732cb7002abd,0x402abd,0x63a0b5c02abd,0x434b3c02abd,0x4d6b2402abd,0x53cb0002abd,0x3d802abd,0x7f802abd,0x4e402abd,0x8ec02abd,0x57002abd,0x9f802abd,0x5a802abd,0xa9c02abd,0x232865402abd,0xaf802abd,0x6b002abd,0x91c02abd,0x6e802abd,0xa1402abd,0x70c02abd,0xaac02abd,0x339c73c02abd,0xafc02abd,0x81402abd,0xa4c02abd,0x83402abd,0xabc02abd,0x95002abd,0xae002abd],[]),([0x2006019,0x74406019,0x2406019,0x86006019,0x9b406019,0xa7c06019,0x1a66006019,0x3c06019,0x74c06019,0x4806019,0x86806019,0x9c006019,0xa8006019,0x3d806019,0x7f806019,0x4e406019,0x8ec06019,0x57006019,0x9f806019,0x5a806019,0xa9c06019,0x6b006019,0x91c06019,0x6e806019,0xa1406019,0x70c06019,0xaac06019,0x81406019,0xa4c06019,0x83406019,0xabc06019,0x95006019,0xae006019],[]),([0x20062b8,0x744062b8,0x24062b8,0x860062b8,0x4dab28062b8,0x53eb04062b8,0xae8062b8,0x3d8062b8,0x7f8062b8,0x4e4062b8,0x8ec062b8,0x570062b8,0x9f8062b8,0x5a8062b8,0xa9c062b8,0x14644062b8,0x6b0062b8,0x91c062b8,0x6e8062b8,0xa14062b8,0x70c062b8,0xaac062b8,0x72c062b8,0xaec062b8,0x814062b8,0xa4c062b8,0x834062b8,0xabc062b8,0x854062b8,0xaf4062b8,0x5a544ac978062b8],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g0 : ∀ q (hq : q < x5s6d0.size), 0 ≤ q → q < 4 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 0 x5s6d0g0c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g4c : List (List ℕ × List ℕ) := [([0x200c8f6,0x4880c8f6,0x300c8f6,0x1fa6600c8f6,0x3c0c8f6,0x1f274c0c8f6,0x480c8f6,0x8680c8f6,0x9c00c8f6,0xa800c8f6,0x3540c8f6,0x8b80c8f6,0x37c0c8f6,0x9d40c8f6,0x3940c8f6,0xa8c0c8f6,0x98fc20c7f80c8f6,0x4e40c8f6,0x8ec0c8f6,0x5700c8f6,0x9f80c8f6,0x5a80c8f6,0xa9c0c8f6,0x6b00c8f6,0x91c0c8f6,0x6e80c8f6,0xa140c8f6,0x70c0c8f6,0xaac0c8f6,0x8140c8f6,0xa4c0c8f6,0x8340c8f6,0xabc0c8f6,0x9500c8f6,0xae00c8f6],[]),([0x5840c95c,0x300c95c,0x6600c95c,0x3c0c95c,0x74c0c95c,0x480c95c,0x8680c95c,0x9c00c95c,0xa800c95c,0x37c0c95c,0x7bc0c95c,0x4c00c95c,0x8d40c95c,0x5540c95c,0xa980c95c,0x3d80c95c,0x7f80c95c,0x4e40c95c,0x8ec0c95c,0xa15d2be9f80c95c,0x5a80c95c,0xa9c0c95c,0x6b00c95c,0x91c0c95c,0x6e80c95c,0xa140c95c,0x70c0c95c,0xaac0c95c,0x8140c95c,0xa4c0c95c,0x8340c95c,0xabc0c95c,0x9500c95c,0xae00c95c],[]),([0x6600c991,0x140300c991,0x3c0c991,0x74c0c991,0x480c991,0x8680c991,0x9c00c991,0xa800c991,0x3a00c991,0x7e40c991,0x4d00c991,0x8e40c991,0x5700c991,0x9f00c991,0x5a80c991,0xa980c991,0x1e23d80c991,0x7f80c991,0x26e4e40c991,0x8ec0c991,0x3249f80c991,0x326a9c0c991,0x6b00c991,0x91c0c991,0x6e80c991,0xa140c991,0x70c0c991,0xaac0c991,0x8140c991,0xa4c0c991,0x8340c991,0xabc0c991,0x9500c991,0xae00c991],[]),([0x180340c998,0x3c0c998,0x74c0c998,0x480c998,0x8680c998,0x9c00c998,0xa800c998,0x1ec3f40c998,0x7f80c998,0x2724f00c998,0x8ec0c998,0x5700c998,0x4fcb740c998,0x5a80c998,0x54eb780c998,0x4840c998,0x7fc0c998,0x5000c998,0x8f00c998,0xa000c998,0xaa00c998,0x6b00c998,0x91c0c998,0x6e80c998,0xa140c998,0x70c0c998,0xaac0c998,0x8140c998,0xa4c0c998,0x8340c998,0xabc0c998,0x9500c998,0xae00c998],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g4 : ∀ q (hq : q < x5s6d0.size), 4 ≤ q → q < 8 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 4 x5s6d0g4c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g8c : List (List ℕ × List ℕ) := [([0x300c9fe,0x6600c9fe,0x3c0c9fe,0x74c0c9fe,0x400c9fe,0x7fc0c9fe,0x480c9fe,0x8680c9fe,0x9c00c9fe,0xa800c9fe,0x98f61f84180c9fe,0x4e40c9fe,0x8ec0c9fe,0x5700c9fe,0x9f80c9fe,0x5a80c9fe,0xa9c0c9fe,0x6b00c9fe,0x91c0c9fe,0x6e80c9fe,0xa140c9fe,0x70c0c9fe,0xaac0c9fe,0x77c0c9fe,0x9440c9fe,0x7b00c9fe,0xa300c9fe,0x7d00c9fe,0xab40c9fe,0x8140c9fe,0xa4c0c9fe,0x8340c9fe,0xabc0c9fe,0x9500c9fe,0xae00c9fe],[]),([0x300ca54,0x6600ca54,0x3c0ca54,0x74c0ca54,0x480ca54,0x8680ca54,0x98c0ca54,0x9c00ca54,0xa800ca54,0x3d80ca54,0x7f80ca54,0x4e40ca54,0x8ec0ca54,0x5540ca54,0x9ec0ca54,0x5700ca54,0x9f80ca54,0x5a80ca54,0xa9c0ca54,0x6b00ca54,0x91c0ca54,0x6e00ca54,0xa0c0ca54,0x6e80ca54,0xa140ca54,0x70c0ca54,0xaac0ca54,0x80c0ca54,0xa440ca54,0x8140ca54,0xa4c0ca54,0x8340ca54,0xabc0ca54,0xba564bcae00ca54],[]),([0x2c0ba56,0x65c0ba56,0x380ba56,0x7480ba56,0x440ba56,0x8640ba56,0x184a69900ba56,0x95c0ba56,0x3d40ba56,0x7f40ba56,0x4e00ba56,0x8e80ba56,0x5500ba56,0x9600ba56,0x56c0ba56,0x9640ba56,0x6400ba56,0x9800ba56,0x6ac0ba56,0x9180ba56,0x6dc0ba56,0x9680ba56,0x6e40ba56,0x96c0ba56,0x7280ba56,0x9840ba56,0x8080ba56,0x9700ba56,0x8100ba56,0x9740ba56,0x8500ba56,0x9880ba56],[]),([0x300ca70,0x6600ca70,0x3c0ca70,0x74c0ca70,0x480ca70,0x8680ca70,0xa800ca70,0x3d80ca70,0x7f80ca70,0x4e40ca70,0x8ec0ca70,0x5700ca70,0x9f80ca70,0x5800ca70,0xa000ca70,0x5a80ca70,0xa9c0ca70,0x6b00ca70,0x91c0ca70,0x6e80ca70,0xa140ca70,0x6ec0ca70,0xa1c0ca70,0x70c0ca70,0xaac0ca70,0x8140ca70,0xa4c0ca70,0x8200ca70,0xa500ca70,0x8340ca70,0xabc0ca70,0x9500ca70,0x570b2c0ca70],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g8 : ∀ q (hq : q < x5s6d0.size), 8 ≤ q → q < 12 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 8 x5s6d0g8c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g12c : List (List ℕ × List ℕ) := [([0x300ca7e,0x330b740ca7e,0x3c0ca7e,0x74c0ca7e,0x480ca7e,0x8680ca7e,0x9c00ca7e,0xa000ca7e,0xa800ca7e,0x3d80ca7e,0x7f80ca7e,0x4e40ca7e,0x8ec0ca7e,0xa15c2ba57c0ca7e,0x5a80ca7e,0xa9c0ca7e,0x6b00ca7e,0x91c0ca7e,0x6e80ca7e,0xa140ca7e,0x6fc0ca7e,0xa300ca7e,0x70c0ca7e,0xaac0ca7e,0x8140ca7e,0xa4c0ca7e,0x8300ca7e,0xa680ca7e,0x8340ca7e,0xabc0ca7e,0x9500ca7e,0xae00ca7e,0x9e80ca7e,0xae80ca7e],[]),([0x300cab8,0x6600cab8,0x3c0cab8,0x74c0cab8,0x480cab8,0x8680cab8,0x4e0b2c0cab8,0x540b080cab8,0x3d80cab8,0x7f80cab8,0x4e40cab8,0x8ec0cab8,0x5700cab8,0x9f80cab8,0x5a80cab8,0xa9c0cab8,0x6440cab8,0xae80cab8,0x6b00cab8,0x91c0cab8,0x6e80cab8,0xa140cab8,0x70c0cab8,0xaac0cab8,0x72c0cab8,0xaec0cab8,0x8140cab8,0xa4c0cab8,0x8340cab8,0xabc0cab8,0x8540cab8,0xaf40cab8,0xba544ac9780cab8],[]),([0x300caba,0x330b7c0caba,0x3c0caba,0x74c0caba,0x480caba,0x8680caba,0x9c00caba,0xa800caba,0x3d80caba,0x7f80caba,0x4e40caba,0x8ec0caba,0x5700caba,0x9f80caba,0x5a80caba,0xa9c0caba,0x6b00caba,0x91c0caba,0x6e80caba,0xa140caba,0x70c0caba,0xaac0caba,0x153987340caba,0xaf00caba,0x8140caba,0xa4c0caba,0x8340caba,0xabc0caba,0x1642c85c0caba,0xaf80caba,0x9500caba,0xae00caba],[]),([0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x1662c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2c2,0x2e9592fac2,0x32a815c2c2],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g12 : ∀ q (hq : q < x5s6d0.size), 12 ≤ q → q < 16 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 12 x5s6d0g12c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g16c : List (List ℕ × List ℕ) := [([0x680f205,0x6640f205,0x6c0f205,0x7500f205,0x8280f205,0x480f205,0x87c0f205,0x700f205,0x9c00f205,0xa840f205,0x3d80f205,0x7f80f205,0x4c00f205,0x8cc0f205,0x4e40f205,0x8ec0f205,0x5700f205,0x9f80f205,0x5a80f205,0xa9c0f205,0x6a40f205,0x90c0f205,0x6b00f205,0x91c0f205,0x6e80f205,0xa140f205,0x70c0f205,0xaac0f205,0x80c0f205,0xab80f205,0xea0640ea4c0f205,0x8340f205,0xabc0f205,0x9500f205,0xae00f205],[]),([0x680f2ae,0x6640f2ae,0x6c0f2ae,0x7500f2ae,0x480f2ae,0x87c0f2ae,0x700f2ae,0x9c00f2ae,0x542b0c0f2ae,0x3d80f2ae,0x7f80f2ae,0x4e40f2ae,0x8ec0f2ae,0x5700f2ae,0x9f80f2ae,0x5a80f2ae,0x54eb180f2ae,0x63c0f2ae,0xacc0f2ae,0x6b00f2ae,0x91c0f2ae,0x6e80f2ae,0xa140f2ae,0x70c0f2ae,0x556b1c0f2ae,0x7240f2ae,0xad40f2ae,0x8140f2ae,0xa4c0f2ae,0x41a8380f2ae,0xabc0f2ae,0x8540f2ae,0x4a89540f2ae,0xae00f2ae,0x9a80f2ae],[]),([0x801182f,0x86c1182f,0x841182f,0x9b01182f,0xa8c1182f,0x487541182f,0x941182f,0x8701182f,0x9c1182f,0x9b41182f,0xa9c1182f,0x3d81182f,0x7f81182f,0x4e41182f,0x8ec1182f,0x5701182f,0x9f81182f,0x545a81182f,0x6b01182f,0x91c1182f,0x6e81182f,0xa141182f,0x70c1182f,0xaac1182f,0x8141182f,0xa4c1182f,0x8341182f,0xabc1182f,0x9501182f,0xae01182f],[]),([0x8011854,0x86c11854,0x8411854,0x9b011854,0xa8c11854,0xbc11854,0x67811854,0xdc11854,0x75811854,0x10411854,0x87c11854,0x11c11854,0x9c011854,0x3d811854,0x7f811854,0x4e411854,0x8ec11854,0x57011854,0x9f811854,0x5a811854,0xa9c11854,0x6b011854,0x91c11854,0x6e811854,0xa1411854,0x70c11854,0xaac11854,0x81411854,0xa4c11854,0x83411854,0xabc11854,0x95011854,0xae011854],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g16 : ∀ q (hq : q < x5s6d0.size), 16 ≤ q → q < 20 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 16 x5s6d0g16c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g20c : List (List ℕ × List ℕ) := [([0x80118f6,0x86c118f6,0x84118f6,0x9b0118f6,0xa8c118f6,0x354118f6,0x8b8118f6,0x37c118f6,0x9d4118f6,0x394118f6,0x110fc20c7f8118f6,0x4e4118f6,0x8ec118f6,0x570118f6,0x9f8118f6,0x5a8118f6,0xa9c118f6,0x6b0118f6,0x91c118f6,0x6e8118f6,0xa14118f6,0x70c118f6,0xaac118f6,0x814118f6,0xa4c118f6,0x834118f6,0xabc118f6,0x950118f6,0xae0118f6],[]),([0x8c17837,0xf417837,0x7075417837,0x9417837,0x87017837,0x9c17837,0x9b417837,0xa9c17837,0x6066c17837,0xcc17837,0x87417837,0xd017837,0x9b817837,0xaac17837,0x3d817837,0x7f817837,0x4e417837,0x8ec17837,0x57017837,0x9f817837,0x545a817837,0x6b017837,0x91c17837,0x6e817837,0xa1417837,0x6c70c17837,0x81417837,0xa4c17837,0x83417837,0xabc17837,0x95017837,0xae017837],[]),([0x5e150b502a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x56134c282a,0x1882a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a],[]),([0x8c17854,0x75417854,0x9417854,0x87017854,0x9c17854,0x9b417854,0xa9c17854,0x6267817854,0xdc17854,0x75817854,0x10417854,0x87c17854,0x11c17854,0x9c017854,0x3d817854,0x7f817854,0x4e417854,0x8ec17854,0x57017854,0x9f817854,0x545a817854,0x6b017854,0x91c17854,0x6e817854,0xa1417854,0x70c17854,0xaac17854,0x81417854,0xa4c17854,0x83417854,0xabc17854,0x95017854,0xae017854],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g20 : ∀ q (hq : q < x5s6d0.size), 20 ≤ q → q < 24 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 20 x5s6d0g20c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g24c : List (List ℕ × List ℕ) := [([0x31,0x31,0x31,0x31,0x31,0x31,0x171031,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x15031,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31,0x31],[]),([0x5e308b502a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x56304c282a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x1402a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a,0x2a],[]),([0x8c178c2,0x754178c2,0x94178c2,0x870178c2,0x9c178c2,0x9b4178c2,0xa9c178c2,0x2dc178c2,0x770178c2,0x2e0178c2,0x898178c2,0x2e4178c2,0x9c8178c2,0x2e8178c2,0x3d8178c2,0x7f8178c2,0x4e4178c2,0x8ec178c2,0x570178c2,0x9f8178c2,0x545a8178c2,0x6b0178c2,0x91c178c2,0x6e8178c2,0xa14178c2,0x70c178c2,0xaac178c2,0x814178c2,0xa4c178c2,0x834178c2,0xabc178c2,0x950178c2,0xae0178c2],[]),([0x8c178f6,0x490178f6,0x1f4754178f6,0x94178f6,0x870178f6,0x9c178f6,0x9b4178f6,0xa9c178f6,0x354178f6,0x8b8178f6,0x37c178f6,0x9d4178f6,0x394178f6,0xa8c178f6,0x148fc20c7f8178f6,0x4e4178f6,0x8ec178f6,0x570178f6,0x9f8178f6,0x545a8178f6,0x6b0178f6,0x91c178f6,0x6e8178f6,0xa14178f6,0x70c178f6,0xaac178f6,0x814178f6,0xa4c178f6,0x834178f6,0xabc178f6,0x950178f6,0xae0178f6],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g24 : ∀ q (hq : q < x5s6d0.size), 24 ≤ q → q < 28 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 24 x5s6d0g24c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g28c : List (List ℕ × List ℕ) := [([0x460a81796a,0x3aa0a81796a,0x4a0a81796a,0x4380a81796a,0x4e0a81796a,0x4da0a81796a,0xacb618554e0a81796a,0x1ca0a81796a,0x3f00a81796a,0x2640a81796a,0x46e0a81796a,0x2aa0a81796a,0x4f80a81796a,0x1ec0a81796a,0x3fc0a81796a,0x2720a81796a,0x4760a81796a,0x2b80a81796a,0x4fc0a81796a,0x3580a81796a,0x48e0a81796a,0x3740a81796a,0x50a0a81796a,0x3860a81796a,0x5560a81796a,0x40a0a81796a,0x5260a81796a,0x41a0a81796a,0x55e0a81796a,0x4a80a81796a,0x5700a81796a],[]),([0x460bc1899e,0x3aa0bc1899e,0x4a0bc1899e,0x4380bc1899e,0x4e0bc1899e,0x4da0bc1899e,0x2a75c40bc1899e,0x1ec0bc1899e,0x3fc0bc1899e,0x2720bc1899e,0x4760bc1899e,0x2b80bc1899e,0x4fc0bc1899e,0x2a2d40bc1899e,0x2500bc1899e,0x4000bc1899e,0x2860bc1899e,0x47c0bc1899e,0x2c60bc1899e,0x5000bc1899e,0x3580bc1899e,0x48e0bc1899e,0x3740bc1899e,0x50a0bc1899e,0x3860bc1899e,0x5560bc1899e,0x40a0bc1899e,0x5260bc1899e,0x41a0bc1899e,0x55e0bc1899e,0x4a80bc1899e,0x5700bc1899e],[]),([0x80179ac,0x6c8179ac,0x8c179ac,0x754179ac,0x94179ac,0x870179ac,0x9c179ac,0x9b4179ac,0xa9c179ac,0x354179ac,0x6479c179ac,0x3d8179ac,0x7f8179ac,0x4e4179ac,0x8ec179ac,0x570179ac,0x9f8179ac,0x545a8179ac,0x6a4179ac,0xa08179ac,0x6a8179ac,0xaa8179ac,0x169ae35e91c179ac,0x6e8179ac,0xa14179ac,0x70c179ac,0xaac179ac,0x814179ac,0xa4c179ac,0x834179ac,0xabc179ac,0x950179ac,0xae0179ac],[]),([0x720179c3,0x8c179c3,0x754179c3,0x94179c3,0x870179c3,0x9c179c3,0x9b4179c3,0xa9c179c3,0x394179c3,0x7dc179c3,0x3d8179c3,0x7f8179c3,0x4e4179c3,0x8ec179c3,0x570179c3,0x9f8179c3,0x545a8179c3,0x6a8179c3,0x914179c3,0x6e0179c3,0xa10179c3,0x6b0179c3,0x91c179c3,0x6e8179c3,0xa14179c3,0x171c538caac179c3,0x814179c3,0xa4c179c3,0x834179c3,0xabc179c3,0x950179c3,0xae0179c3],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g28 : ∀ q (hq : q < x5s6d0.size), 28 ≤ q → q < 32 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 28 x5s6d0g28c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g32c : List (List ℕ × List ℕ) := [([0x46090179d5,0x94179d5,0x870179d5,0x9c179d5,0x9b4179d5,0xa9c179d5,0x1ec3e8179d5,0x7f8179d5,0x490179d5,0x4e4179d5,0x8ec179d5,0x570179d5,0x9f8179d5,0x545a8179d5,0x6b0179d5,0x91c179d5,0x6e8179d5,0xa14179d5,0x70c179d5,0x556b60179d5,0x6c4179d5,0x920179d5,0x6f0179d5,0xa18179d5,0xab4179d5,0x814179d5,0xa4c179d5,0x834179d5,0xabc179d5,0x950179d5,0xae0179d5],[]),([0x8c179d6,0x754179d6,0x94179d6,0x870179d6,0x9c179d6,0x9b4179d6,0xa9c179d6,0x3d8179d6,0x7f8179d6,0x490179d6,0x800179d6,0x4e4179d6,0x8ec179d6,0x570179d6,0x9f8179d6,0x545a8179d6,0x6b0179d6,0x91c179d6,0x6e8179d6,0xa14179d6,0x70c179d6,0x556b64179d6,0x6cc179d6,0x924179d6,0x6f4179d6,0xa1c179d6,0x814179d6,0xa4c179d6,0x834179d6,0xabc179d6,0x950179d6,0xae0179d6],[]),([0x8c179fe,0x754179fe,0x94179fe,0x870179fe,0x9c179fe,0x9b4179fe,0xa9c179fe,0x148f61f8418179fe,0x4e4179fe,0x8ec179fe,0x570179fe,0x9f8179fe,0x545a8179fe,0x6b0179fe,0x91c179fe,0x6e8179fe,0xa14179fe,0x70c179fe,0xaac179fe,0x77c179fe,0x944179fe,0x7b0179fe,0xa30179fe,0x7d0179fe,0xab4179fe,0x814179fe,0xa4c179fe,0x834179fe,0xabc179fe,0x950179fe,0xae0179fe],[]),([0x8c17a47,0x75417a47,0x9417a47,0x87017a47,0x9817a47,0x92017a47,0x9c17a47,0x9b417a47,0xa9c17a47,0x3d817a47,0x7f817a47,0x4e417a47,0x8ec17a47,0x53017a47,0x94417a47,0x57017a47,0x9f817a47,0x545a817a47,0x169ac35c6bc17a47,0x6e817a47,0xa1417a47,0x70c17a47,0xaac17a47,0x81417a47,0xa4c17a47,0x83417a47,0xabc17a47,0x90417a47,0xa7017a47,0x91017a47,0xad817a47,0x95017a47,0xae017a47],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g32 : ∀ q (hq : q < x5s6d0.size), 32 ≤ q → q < 36 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 32 x5s6d0g32c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g36c : List (List ℕ × List ℕ) := [([0x8c17aa7,0x75417aa7,0x9417aa7,0x87017aa7,0x9c17aa7,0x9b417aa7,0x3d817aa7,0x7f817aa7,0x4e417aa7,0x8ec17aa7,0x57017aa7,0x9f817aa7,0xa81596a2d861417aa7,0x6b017aa7,0x91c17aa7,0x6e817aa7,0xa1417aa7,0x70c17aa7,0xaac17aa7,0x71c17aa7,0xab417aa7,0x81417aa7,0xa4c17aa7,0x83417aa7,0xabc17aa7,0x84017aa7,0xad017aa7,0x95017aa7,0xae017aa7,0x99817aa7,0xae817aa7],[]),([0x8c17aab,0x3aab6017aab,0x9417aab,0x87017aab,0x9c17aab,0x9b417aab,0xa9c17aab,0xab417aab,0x3d817aab,0x7f817aab,0x4e417aab,0x8ec17aab,0x57017aab,0x9f817aab,0x545a817aab,0x5863017aab,0x6b017aab,0x91c17aab,0x6e817aab,0xa1417aab,0x171c338a71817aab,0x81417aab,0xa4c17aab,0x83417aab,0xabc17aab,0x84417aab,0xad817aab,0x95017aab,0xae017aab,0x99c17aab,0xaec17aab],[]),([0xbc1e854,0x66c1e854,0xdc1e854,0x7541e854,0xe41e854,0x8781e854,0xec1e854,0x9bc1e854,0xab41e854,0x6781e854,0x7581e854,0x1041e854,0x87c1e854,0x11c1e854,0x9c01e854,0x3d81e854,0x7f81e854,0x4e41e854,0x8ec1e854,0x5701e854,0x9f81e854,0x5a81e854,0xa9c1e854,0x6b01e854,0x91c1e854,0x6e81e854,0xa141e854,0x70c1e854,0xaac1e854,0x8141e854,0xa4c1e854,0x8341e854,0xabc1e854,0x9501e854,0xae01e854],[]),([0xbc1e9fe,0x66c1e9fe,0xdc1e9fe,0x7541e9fe,0xe41e9fe,0x8781e9fe,0xec1e9fe,0x9bc1e9fe,0xab41e9fe,0x1e0f61f84181e9fe,0x4e41e9fe,0x8ec1e9fe,0x5701e9fe,0x9f81e9fe,0x5a81e9fe,0xa9c1e9fe,0x6b01e9fe,0x91c1e9fe,0x6e81e9fe,0xa141e9fe,0x70c1e9fe,0xaac1e9fe,0x77c1e9fe,0x9441e9fe,0x7b01e9fe,0xa301e9fe,0x7d01e9fe,0x8141e9fe,0xa4c1e9fe,0x8341e9fe,0xabc1e9fe,0x9501e9fe,0xae01e9fe],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g36 : ∀ q (hq : q < x5s6d0.size), 36 ≤ q → q < 40 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 36 x5s6d0g36c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g40c : List (List ℕ × List ℕ) := [([0x802a0d5,0x3702a0d5,0xbc2a0d5,0x6782a0d5,0xdc2a0d5,0x7582a0d5,0x1042a0d5,0x87c2a0d5,0x11c2a0d5,0x9c02a0d5,0x3482a0d5,0x561ae9cc2a0d5,0x34c2a0d5,0x551aca882a0d5,0x3d82a0d5,0x7f82a0d5,0x4e42a0d5,0x8ec2a0d5,0x5702a0d5,0x9f82a0d5,0x5a82a0d5,0xa9c2a0d5,0x6b02a0d5,0x91c2a0d5,0x6e82a0d5,0xa142a0d5,0x70c2a0d5,0xaac2a0d5,0x8142a0d5,0xa4c2a0d5,0x8342a0d5,0xabc2a0d5,0x9502a0d5,0xae02a0d5],[]),([0x4b02a0e5,0xbc2a0e5,0x6782a0e5,0xdc2a0e5,0x7582a0e5,0x1042a0e5,0x87c2a0e5,0x11c2a0e5,0x9c02a0e5,0x34c2a0e5,0x581ce8b42a0e5,0x3742a0e5,0x571cc9d02a0e5,0x3d82a0e5,0x7f82a0e5,0x4e42a0e5,0x8ec2a0e5,0x5702a0e5,0x9f82a0e5,0x5a82a0e5,0xa9c2a0e5,0x6b02a0e5,0x91c2a0e5,0x6e82a0e5,0xa142a0e5,0x70c2a0e5,0xaac2a0e5,0x8142a0e5,0xa4c2a0e5,0x8342a0e5,0xabc2a0e5,0x9502a0e5,0xae02a0e5],[]),([0x8c2a0f6,0x4b02a0f6,0xbc2a0f6,0x6782a0f6,0xdc2a0f6,0x7582a0f6,0x1042a0f6,0x87c2a0f6,0x11c2a0f6,0x9c02a0f6,0x3542a0f6,0x8b82a0f6,0x37c2a0f6,0x9d42a0f6,0x3942a0f6,0xa8c2a0f6,0x250fc20c7f82a0f6,0x4e42a0f6,0x8ec2a0f6,0x5702a0f6,0x9f82a0f6,0x5a82a0f6,0xa9c2a0f6,0x6b02a0f6,0x91c2a0f6,0x6e82a0f6,0xa142a0f6,0x70c2a0f6,0xaac2a0f6,0x8142a0f6,0xa4c2a0f6,0x8342a0f6,0xabc2a0f6,0x9502a0f6,0xae02a0f6],[]),([0x88250fc,0x3a4250fc,0xa4250fc,0x3fc250fc,0xf0250fc,0x428250fc,0xfc250fc,0x434250fc,0x10c250fc,0x454250fc,0x350250fc,0x440250fc,0x378250fc,0x458250fc,0x38c250fc,0x46c250fc,0x3ac250fc,0x444250fc,0x3b4250fc,0x45c250fc,0x3c0250fc,0x470250fc,0x41c250fc,0x44c250fc,0x420250fc,0x464250fc,0x424250fc,0x478250fc,0x42c250fc,0x468250fc,0x430250fc,0x47c250fc,0x450250fc,0x480250fc],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g40 : ∀ q (hq : q < x5s6d0.size), 40 ≤ q → q < 44 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 40 x5s6d0g40c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g44c : List (List ℕ × List ℕ) := [([0xbc2a124,0x4b02a124,0x24a6782a124,0xdc2a124,0x7582a124,0x1042a124,0x87c2a124,0x11c2a124,0x9c02a124,0x3d82a124,0x7542a124,0x3682a124,0x8bc2a124,0x3802a124,0x9d82a124,0x3942a124,0xa9c2a124,0x24c7f82a124,0x4e42a124,0x8ec2a124,0x5702a124,0x9f82a124,0x2465a82a124,0x6b02a124,0x91c2a124,0x6e82a124,0xa142a124,0x70c2a124,0xaac2a124,0x8142a124,0xa4c2a124,0x8342a124,0xabc2a124,0x9502a124,0xae02a124],[]),([0xbc2a12c,0x6782a12c,0xdc2a12c,0x7582a12c,0x1042a12c,0x87c2a12c,0x11c2a12c,0x9c02a12c,0x4902a12c,0x4a02a12c,0x36c2a12c,0x8c02a12c,0x3842a12c,0x9dc2a12c,0x3942a12c,0x3d82a12c,0x7f82a12c,0x4e42a12c,0x8ec2a12c,0x5702a12c,0x9f82a12c,0x5a82a12c,0xa9c2a12c,0x6b02a12c,0x91c2a12c,0x6e82a12c,0xa142a12c,0x70c2a12c,0xaac2a12c,0x8142a12c,0xa4c2a12c,0x8342a12c,0xabc2a12c,0x9502a12c,0xae02a12c],[]),([0x982a14c,0x5482a14c,0xbc2a14c,0x29a6782a14c,0xdc2a14c,0x7582a14c,0x1042a14c,0x87c2a14c,0x11c2a14c,0x9c02a14c,0x3d82a14c,0x7a42a14c,0x4e42a14c,0x8b82a14c,0x5182a14c,0x9e42a14c,0x5202a14c,0xa942a14c,0x29c7f82a14c,0x29e8ec2a14c,0x2925702a14c,0x9f82a14c,0x2945a82a14c,0xa9c2a14c,0x6b02a14c,0x91c2a14c,0x6e82a14c,0xa142a14c,0x70c2a14c,0xaac2a14c,0x8142a14c,0xa4c2a14c,0x8342a14c,0xabc2a14c,0x9502a14c,0xae02a14c],[]),([0x6782a16a,0x540bc2a16a,0xdc2a16a,0x7582a16a,0x1042a16a,0x87c2a16a,0x11c2a16a,0x9c02a16a,0x3942a16a,0x7e02a16a,0x4c82a16a,0x8dc2a16a,0x5542a16a,0x9f02a16a,0x3d82a16a,0x7f82a16a,0x4e42a16a,0x8ec2a16a,0x5702a16a,0x9f82a16a,0x2696c30aa9c2a16a,0x6b02a16a,0x91c2a16a,0x6e82a16a,0xa142a16a,0x70c2a16a,0xaac2a16a,0x8142a16a,0xa4c2a16a,0x8342a16a,0xabc2a16a,0x9502a16a,0xae02a16a],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g44 : ∀ q (hq : q < x5s6d0.size), 44 ≤ q → q < 48 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 44 x5s6d0g44c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g48c : List (List ℕ × List ℕ) := [([0x5b42696c,0xac2696c,0xd42696c,0x5c82696c,0x1002696c,0x5e42696c,0x1102696c,0x5fc2696c,0x3902696c,0x5d02696c,0x4c42696c,0x5e82696c,0x54c2696c,0x6042696c,0x3bc2696c,0x5d42696c,0x4d42696c,0x5ec2696c,0x5642696c,0x6082696c,0x5b82696c,0x5f02696c,0x5bc2696c,0x60c2696c,0x5c42696c,0x61c2696c,0x5d82696c,0x6102696c,0x5e02696c,0x6242696c,0x5f82696c,0x62c2696c],[]),([0x2dab8826985,0xd426985,0x5c826985,0x10026985,0x5e426985,0x11026985,0x5fc26985,0x540ac26985,0x39026985,0x5d026985,0x4c426985,0x5e826985,0x54c26985,0x60426985,0x5b826985,0x5f026985,0x5bc26985,0x60c26985,0x5c026985,0x61826985,0x5c426985,0x61c26985,0x5d826985,0x61026985,0x5dc26985,0x62026985,0x5e026985,0x62426985,0x5f426985,0x62826985,0x5f826985,0x62c26985],[]),([0x8c2a18c,0x6782a18c,0x580bc2a18c,0xdc2a18c,0x7582a18c,0x1042a18c,0x87c2a18c,0x11c2a18c,0x9c02a18c,0x3d82a18c,0x7e02a18c,0x4cc2a18c,0x8e02a18c,0x5602a18c,0x9f42a18c,0x5a82a18c,0xa8c2a18c,0x31a7f82a18c,0x26c4e42a18c,0x8ec2a18c,0x2b45702a18c,0x9f82a18c,0x31ca9c2a18c,0x6b02a18c,0x91c2a18c,0x6e82a18c,0xa142a18c,0x70c2a18c,0xaac2a18c,0x8142a18c,0xa4c2a18c,0x8342a18c,0xabc2a18c,0x9502a18c,0xae02a18c],[]),([0x5e0c02a19b,0x6782a19b,0xf42a19b,0xdc2a19b,0x7582a19b,0x1042a19b,0x87c2a19b,0x11c2a19b,0x9c02a19b,0x1ec3f82a19b,0x7f82a19b,0x4e42a19b,0x8ec2a19b,0x5702a19b,0x9f82a19b,0x5a82a19b,0x54eb802a19b,0x4a02a19b,0x5082a19b,0x8f42a19b,0x5882a19b,0x9fc2a19b,0xab42a19b,0x6b02a19b,0x91c2a19b,0x6e82a19b,0xa142a19b,0x70c2a19b,0xaac2a19b,0x8142a19b,0xa4c2a19b,0x8342a19b,0xabc2a19b,0x9502a19b,0xae02a19b],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g48 : ∀ q (hq : q < x5s6d0.size), 48 ≤ q → q < 52 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 48 x5s6d0g48c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g52c : List (List ℕ × List ℕ) := [([0x5e0c42a19e,0xdc2a19e,0x7582a19e,0x1042a19e,0x87c2a19e,0x11c2a19e,0x9c02a19e,0x3d82a19e,0x7f82a19e,0x4e42a19e,0x8ec2a19e,0x5702a19e,0x9f82a19e,0x5a82a19e,0x54eb882a19e,0x4a02a19e,0x8002a19e,0x50c2a19e,0x8f82a19e,0x58c2a19e,0xa002a19e,0x6b02a19e,0x91c2a19e,0x6e82a19e,0xa142a19e,0x70c2a19e,0xaac2a19e,0x8142a19e,0xa4c2a19e,0x8342a19e,0xabc2a19e,0x9502a19e,0xae02a19e],[]),([0x5e0c82a1e7,0x6782a1e7,0xdc2a1e7,0x7582a1e7,0xe82a1e7,0x7a02a1e7,0x1042a1e7,0x87c2a1e7,0x11c2a1e7,0x9c02a1e7,0x1ec4102a1e7,0x7f82a1e7,0x2724f42a1e7,0x8ec2a1e7,0x5702a1e7,0x4fcb942a1e7,0x5a82a1e7,0x54eb982a1e7,0x6d42a1e7,0x6b02a1e7,0x91c2a1e7,0x6e82a1e7,0xa142a1e7,0x70c2a1e7,0xaac2a1e7,0x77c2a1e7,0x78c2a1e7,0xa202a1e7,0x7982a1e7,0xab02a1e7,0x8142a1e7,0xa4c2a1e7,0x8342a1e7,0xabc2a1e7,0x9502a1e7,0xae02a1e7],[]),([0xbc2a1f4,0x6782a1f4,0xdc2a1f4,0x7582a1f4,0x8002a1f4,0x1042a1f4,0x87c2a1f4,0x11c2a1f4,0x9c02a1f4,0x3d82a1f4,0x7f82a1f4,0x5a82a1f4,0x7dc2a1f4,0x4e42a1f4,0x8ec2a1f4,0x5702a1f4,0x9f82a1f4,0x3eaa9c2a1f4,0x70c2a1f4,0x7e02a1f4,0x6b02a1f4,0x91c2a1f4,0x6e82a1f4,0xa142a1f4,0x3ecaac2a1f4,0x7742a1f4,0x93c2a1f4,0x7a82a1f4,0xa282a1f4,0x8142a1f4,0xa4c2a1f4,0x3e48342a1f4,0xabc2a1f4,0x3e69502a1f4,0xae02a1f4],[]),([0xbc2a1f7,0x33cb842a1f7,0xdc2a1f7,0x7582a1f7,0x8002a1f7,0x1042a1f7,0x87c2a1f7,0x11c2a1f7,0x9c02a1f7,0x1ec4142a1f7,0x7f82a1f7,0x4e42a1f7,0x476b9c2a1f7,0x5702a1f7,0x4fcba02a1f7,0x2d45cc2a1f7,0xa9c2a1f7,0x71c2a1f7,0x6b02a1f7,0x91c2a1f7,0x6e82a1f7,0xa142a1f7,0x70c2a1f7,0xaac2a1f7,0x7782a1f7,0x9402a1f7,0x7ac2a1f7,0xa2c2a1f7,0x7d02a1f7,0x8142a1f7,0xa4c2a1f7,0x8342a1f7,0xabc2a1f7,0x9502a1f7,0xae02a1f7],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g52 : ∀ q (hq : q < x5s6d0.size), 52 ≤ q → q < 56 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 52 x5s6d0g52c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g56c : List (List ℕ × List ℕ) := [([0xbc2a1fe,0x6782a1fe,0xdc2a1fe,0x7582a1fe,0xf42a1fe,0x8002a1fe,0x1042a1fe,0x87c2a1fe,0x11c2a1fe,0x9c02a1fe,0x250f61f84182a1fe,0x4e42a1fe,0x8ec2a1fe,0x5702a1fe,0x9f82a1fe,0x5a82a1fe,0xa9c2a1fe,0x6b02a1fe,0x91c2a1fe,0x6e82a1fe,0xa142a1fe,0x70c2a1fe,0xaac2a1fe,0x77c2a1fe,0x9442a1fe,0x7b02a1fe,0xa302a1fe,0x7d02a1fe,0xab42a1fe,0x8142a1fe,0xa4c2a1fe,0x8342a1fe,0xabc2a1fe,0x9502a1fe,0xae02a1fe],[]),([0xbc2a200,0x6782a200,0xdc2a200,0x7582a200,0x1042a200,0x87c2a200,0x11c2a200,0x9c02a200,0x3d82a200,0x7f82a200,0x4e42a200,0x8ec2a200,0x5702a200,0x9f82a200,0x5a82a200,0xa9c2a200,0x6b02a200,0x91c2a200,0x6e82a200,0xa142a200,0x70c2a200,0xaac2a200,0x7882a200,0x9482a200,0x7b42a200,0xa342a200,0x7d02a200,0x8142a200,0xa4c2a200,0x8342a200,0xabc2a200,0x9502a200,0xae02a200],[]),([0xbc2a251,0x6782a251,0xdc2a251,0x7582a251,0x1042a251,0x87c2a251,0x1082a251,0x9482a251,0x11c2a251,0x9c02a251,0x3d82a251,0x7f82a251,0x4e42a251,0x8ec2a251,0x5702a251,0x9f82a251,0x5a82a251,0xa9c2a251,0x6b02a251,0x91c2a251,0x6e82a251,0xa142a251,0x70c2a251,0xaac2a251,0x8142a251,0xa4c2a251,0x8342a251,0xabc2a251,0x5049492c2a251,0xa742a251,0x5149a9382a251,0xadc2a251,0x9502a251,0xae02a251],[]),([0xbc2a2a3,0x6782a2a3,0xdc2a2a3,0x7582a2a3,0x1042a2a3,0x87c2a2a3,0x11c2a2a3,0x9c02a2a3,0x8c2a2a3,0x3d82a2a3,0x7f82a2a3,0x4e42a2a3,0x8ec2a2a3,0x5702a2a3,0x9f82a2a3,0x2d45ac2a2a3,0xa9c2a2a3,0x6302a2a3,0x6b02a2a3,0x91c2a2a3,0x6e82a2a3,0xa142a2a3,0x3867102a2a3,0xaac2a2a3,0x71c2a2a3,0x8142a2a3,0xa4c2a2a3,0x8342a2a3,0x55eb102a2a3,0x83c2a2a3,0xac82a2a3,0x9502a2a3,0x570b142a2a3,0x9942a2a3,0xae42a2a3],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g56 : ∀ q (hq : q < x5s6d0.size), 56 ≤ q → q < 60 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 56 x5s6d0g56c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g60c : List (List ℕ × List ℕ) := [([0xbc2a2a7,0x33cb882a2a7,0xdc2a2a7,0x7582a2a7,0x1042a2a7,0x87c2a2a7,0x11c2a2a7,0x9c02a2a7,0x3d82a2a7,0x7f82a2a7,0x4e42a2a7,0x8ec2a2a7,0x5702a2a7,0x9f82a2a7,0x2696a2d86142a2a7,0x6b02a2a7,0x91c2a2a7,0x6e82a2a7,0xa142a2a7,0x70c2a2a7,0xaac2a2a7,0x71c2a2a7,0xab42a2a7,0x8142a2a7,0xa4c2a2a7,0x8342a2a7,0xabc2a2a7,0x8402a2a7,0xad02a2a7,0x9502a2a7,0xae02a2a7,0x9982a2a7,0xae82a2a7],[]),([0xbc2a2ad,0x6782a2ad,0xdc2a2ad,0x7582a2ad,0x1042a2ad,0x87c2a2ad,0x11c2a2ad,0x9c02a2ad,0xf42a2ad,0x3d82a2ad,0x7f82a2ad,0x4e42a2ad,0x8ec2a2ad,0x5702a2ad,0x9f82a2ad,0x5a82a2ad,0xa9c2a2ad,0x6b02a2ad,0x91c2a2ad,0x6e82a2ad,0xa142a2ad,0x70c2a2ad,0xaac2a2ad,0x8142a2ad,0xa4c2a2ad,0x8342a2ad,0xabc2a2ad,0x4f42484c2a2ad,0xadc2a2ad,0x9502a2ad,0xae02a2ad,0x534d09a42a2ad,0xaf02a2ad],[]),([0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x242cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0x2cb,0xa495d2f2cb,0xa89c15c2cb],[]),([0x17031a8e,0x67c31a8e,0x17431a8e,0x75c31a8e,0x10431a8e,0x88831a8e,0x11c31a8e,0x9c431a8e,0xbc17c31a8e,0x3d831a8e,0x7f831a8e,0x4e431a8e,0x8ec31a8e,0x57031a8e,0x9f831a8e,0x59031a8e,0xa6031a8e,0x2d25a831a8e,0xa9c31a8e,0x6b031a8e,0x91c31a8e,0x6e831a8e,0xa1431a8e,0x70031a8e,0xa6c31a8e,0x38470c31a8e,0xaac31a8e,0x81431a8e,0xa4c31a8e,0x83431a8e,0xa4431a8e,0x51eabc31a8e,0x95031a8e,0xa4831a8e,0x520ae031a8e],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g60 : ∀ q (hq : q < x5s6d0.size), 60 ≤ q → q < 64 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 60 x5s6d0g60c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g64c : List (List ℕ × List ℕ) := [([0x17031a93,0x67c31a93,0x17431a93,0x75c31a93,0x10431a93,0x88831a93,0x11c31a93,0x9c431a93,0x12431a93,0x17c31a93,0x3d831a93,0x7f831a93,0x4e431a93,0x8ec31a93,0x57031a93,0x9f831a93,0x59431a93,0xa6831a93,0x5a831a93,0xa9c31a93,0x6b031a93,0x91c31a93,0x6e831a93,0xa1431a93,0x70431a93,0xa7031a93,0x70c31a93,0xaac31a93,0x3120540c81c31a93,0x83431a93,0xabc31a93,0x95031a93,0xae031a93,0xa3831a93,0xaf431a93],[]),([0x19035887,0x76035887,0x19435887,0x88035887,0x9c35887,0x9f835887,0x19835887,0xa9c35887,0xd868835887,0x1c435887,0x76835887,0x1dc35887,0x88835887,0x11c35887,0x1e435887,0x3d835887,0xda7f835887,0x4e435887,0xdc8ec35887,0xd057035887,0xd25a835887,0x6b035887,0x91c35887,0x6e835887,0xa1435887,0x70c35887,0xaac35887,0x81435887,0xa4c35887,0x83435887,0xabc35887,0x95035887,0xae035887],[]),([0x19035a54,0x76035a54,0x19435a54,0x88035a54,0x9ec35a54,0x9c35a54,0x9f835a54,0x19835a54,0xa9c35a54,0x3d835a54,0xda7f835a54,0x4e435a54,0xdc8ec35a54,0xce55435a54,0xd057035a54,0xd25a835a54,0x6b035a54,0x91c35a54,0x6e035a54,0xa0c35a54,0x6e835a54,0xa1435a54,0x70c35a54,0xaac35a54,0x80c35a54,0xa4435a54,0x81435a54,0xa4c35a54,0x83435a54,0xabc35a54,0x352564bcae035a54],[]),([0x190438f6,0x4b8438f6,0x1ac438f6,0x688438f6,0x1c4438f6,0x768438f6,0x1dc438f6,0x888438f6,0x11c438f6,0x1e4438f6,0x354438f6,0x8b8438f6,0x37c438f6,0x9d4438f6,0x394438f6,0xa8c438f6,0x420fc20c7f8438f6,0x4e4438f6,0x8ec438f6,0x570438f6,0x9f8438f6,0x5a8438f6,0xa9c438f6,0x6b0438f6,0x91c438f6,0x6e8438f6,0xa14438f6,0x70c438f6,0xaac438f6,0x814438f6,0xa4c438f6,0x834438f6,0xabc438f6,0x950438f6,0xae0438f6],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g64 : ∀ q (hq : q < x5s6d0.size), 64 ≤ q → q < 68 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 64 x5s6d0g64c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g68c : List (List ℕ × List ℕ) := [([0x68843955,0xce1ac43955,0x1c443955,0x76843955,0x1dc43955,0x88843955,0x11c43955,0x1e443955,0x37443955,0x892ae7b843955,0x4bc43955,0x882ac8d043955,0x3d843955,0x7f843955,0x4e443955,0x8ec43955,0x57043955,0x9f843955,0x5a843955,0xa9c43955,0x6b043955,0x91c43955,0x6e843955,0xa1443955,0x70c43955,0xaac43955,0x81443955,0xa4c43955,0x83443955,0xabc43955,0x95043955,0xae043955],[]),([0x9c4395c,0x6884395c,0xd01ac4395c,0x1c44395c,0x7684395c,0x1dc4395c,0x8884395c,0x11c4395c,0x1e44395c,0x37c4395c,0x7bc4395c,0x4c04395c,0x8d44395c,0x5544395c,0xa984395c,0x3d84395c,0x7f84395c,0x4e44395c,0x8ec4395c,0x4295d2be9f84395c,0x5a84395c,0xa9c4395c,0x6b04395c,0x91c4395c,0x6e84395c,0xa144395c,0x70c4395c,0xaac4395c,0x8144395c,0xa4c4395c,0x8344395c,0xabc4395c,0x9504395c,0xae04395c],[]),([0xd61b0439a2,0x1c4439a2,0x768439a2,0x1dc439a2,0x888439a2,0x11c439a2,0x1e4439a2,0x3d8439a2,0x7f8439a2,0x4e4439a2,0x8ec439a2,0x570439a2,0x9f8439a2,0x5a8439a2,0xa9c439a2,0x4b4439a2,0x804439a2,0x510439a2,0x8fc439a2,0x58c439a2,0x680439a2,0x6b0439a2,0x91c439a2,0x6e8439a2,0xa14439a2,0x70c439a2,0xaac439a2,0x814439a2,0xa4c439a2,0x834439a2,0xabc439a2,0x950439a2,0xae0439a2],[]),([0xd61b4439fe,0x688439fe,0xe21c8439fe,0x768439fe,0x1cc439fe,0x804439fe,0x1dc439fe,0x888439fe,0x11c439fe,0x1e4439fe,0x420f61f8418439fe,0x4e4439fe,0x8ec439fe,0x570439fe,0x9f8439fe,0x5a8439fe,0xa9c439fe,0x6b0439fe,0x91c439fe,0x6e8439fe,0xa14439fe,0x70c439fe,0xaac439fe,0x77c439fe,0x944439fe,0x7b0439fe,0xa30439fe,0x7d0439fe,0xab4439fe,0x814439fe,0xa4c439fe,0x834439fe,0xabc439fe,0x950439fe,0xae0439fe],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g68 : ∀ q (hq : q < x5s6d0.size), 68 ≤ q → q < 72 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 68 x5s6d0g68c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g72c : List (List ℕ × List ℕ) := [([0x1ac43a54,0x68843a54,0x1c443a54,0x76843a54,0x1dc43a54,0x88843a54,0x8a11c43a54,0xf01e443a54,0x3d843a54,0x7f843a54,0x4e443a54,0x8ec43a54,0x55443a54,0x9ec43a54,0x57043a54,0x9f843a54,0x5a843a54,0xa9c43a54,0x6b043a54,0x91c43a54,0x6e043a54,0xa0c43a54,0x6e843a54,0xa1443a54,0x70c43a54,0xaac43a54,0x80c43a54,0xa4443a54,0x81443a54,0xa4c43a54,0x83443a54,0xabc43a54,0x432564bcae043a54],[]),([0x1a843256,0x68443256,0x1c043256,0x76443256,0x1d843256,0x88443256,0x11843256,0x8010220843256,0x3d443256,0x7f443256,0x4e043256,0x8e843256,0x55043256,0x96043256,0x56c43256,0x96443256,0x64043256,0x98043256,0x6ac43256,0x91843256,0x6dc43256,0x96843256,0x6e443256,0x96c43256,0x72843256,0x98443256,0x80843256,0x97043256,0x81043256,0x97443256,0x85043256,0x98843256],[]),([0x1ac43a7b,0x344b8c43a7b,0x1c443a7b,0x76843a7b,0x1dc43a7b,0x88843a7b,0x11c43a7b,0x1e443a7b,0x3d843a7b,0x3fcba443a7b,0x4e443a7b,0x476bac43a7b,0x2b857843a7b,0x9f843a7b,0x2d460043a7b,0xa9c43a7b,0x6b043a7b,0x91c43a7b,0x6e843a7b,0xa1443a7b,0x6f843a7b,0xa2443a7b,0x70c43a7b,0xaac43a7b,0x81443a7b,0xa4c43a7b,0x82c43a7b,0xa6443a7b,0x83443a7b,0xabc43a7b,0x99843a7b,0x95043a7b,0xae043a7b,0x9e843a7b],[]),([0x1ac43a7e,0x68843a7e,0x1c443a7e,0x76843a7e,0x1dc43a7e,0x88843a7e,0x11c43a7e,0x1bc43a7e,0x1e443a7e,0x3d843a7e,0x7f843a7e,0x4e443a7e,0x8ec43a7e,0x4295c2ba57c43a7e,0x5a843a7e,0xa9c43a7e,0x6b043a7e,0x91c43a7e,0x6e843a7e,0xa1443a7e,0x6fc43a7e,0xa3043a7e,0x70c43a7e,0xaac43a7e,0x81443a7e,0xa4c43a7e,0x83043a7e,0xa6843a7e,0x83443a7e,0xabc43a7e,0x95043a7e,0xae043a7e,0x9e843a7e,0xae843a7e],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g72 : ∀ q (hq : q < x5s6d0.size), 72 ≤ q → q < 76 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 72 x5s6d0g72c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g76c : List (List ℕ × List ℕ) := [([0x1ac43ab8,0x68843ab8,0x1c443ab8,0x76843ab8,0x1dc43ab8,0x88843ab8,0x11c43ab8,0x1e443ab8,0x20c43ab8,0x3d843ab8,0x7f843ab8,0x4e443ab8,0x8ec43ab8,0x57043ab8,0x9f843ab8,0x5a843ab8,0xa9c43ab8,0x64443ab8,0xae843ab8,0x6b043ab8,0x91c43ab8,0x6e843ab8,0xa1443ab8,0x70c43ab8,0xaac43ab8,0x72c43ab8,0xaec43ab8,0x81443ab8,0xa4c43ab8,0x83443ab8,0xabc43ab8,0x85443ab8,0xaf443ab8,0x432544ac97843ab8],[]),([0x9112424c52a03,0x68c52a03,0x9512c25c52a03,0x76c52a03,0xe81dc52a03,0x13226c52a03,0x14228852a03,0x3d852a03,0x7f852a03,0x4bc52a03,0xa7464ba852a03,0x4e452a03,0x8ec52a03,0x57052a03,0x9f852a03,0x5a852a03,0xa9c52a03,0x6a052a03,0xa6484b6852a03,0x6b052a03,0x91c52a03,0x6e852a03,0xa1452a03,0x70c52a03,0xaac52a03,0x81452a03,0xa4c52a03,0x83452a03,0xabc52a03,0x95052a03,0xae052a03],[]),([0x9112425052a05,0x68c52a05,0x9512c26052a05,0x76c52a05,0xf852a05,0xea1dc52a05,0x13426c52a05,0x28852a05,0x3d852a05,0x7f852a05,0x4c052a05,0x8cc52a05,0x4e452a05,0x8ec52a05,0x57052a05,0x9f852a05,0x5a852a05,0xa9c52a05,0x6a452a05,0x90c52a05,0x6b052a05,0x91c52a05,0x6e852a05,0xa1452a05,0x70c52a05,0xaac52a05,0x80c52a05,0xab852a05,0x5220640ea4c52a05,0x83452a05,0xabc52a05,0x95052a05,0xae052a05],[]),([0x3486a8f6,0xd71f09cc6a8f6,0x34c6a8f6,0xd61eea886a8f6,0x1b08b86a8f6,0x37c6a8f6,0x9d46a8f6,0x3946a8f6,0xa8c6a8f6,0x6a0fc20c7f86a8f6,0x4e46a8f6,0x8ec6a8f6,0x5706a8f6,0x9f86a8f6,0x5a86a8f6,0xa9c6a8f6,0x6b06a8f6,0x91c6a8f6,0x6e86a8f6,0xa146a8f6,0x70c6a8f6,0xaac6a8f6,0x8146a8f6,0xa4c6a8f6,0x8346a8f6,0xabc6a8f6,0x9506a8f6,0xae06a8f6],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g76 : ∀ q (hq : q < x5s6d0.size), 76 ≤ q → q < 80 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 76 x5s6d0g76c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g80c : List (List ℕ × List ℕ) := [([0x3547b12c,0x8b87b12c,0x37c7b12c,0x9d47b12c,0x3947b12c,0xa8c7b12c,0x4907b12c,0x6787b12c,0x4a07b12c,0x7587b12c,0x36c7b12c,0x8c07b12c,0x3847b12c,0x9dc7b12c,0x748fc20c7f87b12c,0x4e47b12c,0x8ec7b12c,0x5707b12c,0x9f87b12c,0x5a87b12c,0xa9c7b12c,0x6b07b12c,0x91c7b12c,0x6e87b12c,0xa147b12c,0x70c7b12c,0xaac7b12c,0x8147b12c,0xa4c7b12c,0x8347b12c,0xabc7b12c,0x9507b12c,0xae07b12c],[]),([0x3547b139,0x5307b139,0x2748b87b139,0x37c7b139,0x9d47b139,0x3947b139,0xa8c7b139,0x1f67a47b139,0x4c07b139,0x9e07b139,0x4c87b139,0xa907b139,0x758fc20c7f87b139,0x7513b27e8ec7b139,0x5707b139,0x9f87b139,0x5a87b139,0xa9c7b139,0x6b07b139,0x91c7b139,0x6e87b139,0xa147b139,0x70c7b139,0xaac7b139,0x8147b139,0xa4c7b139,0x8347b139,0xabc7b139,0x9507b139,0xae07b139],[]),([0x3547b19e,0x8b87b19e,0x37c7b19e,0x9d47b19e,0x3947b19e,0xa8c7b19e,0x7e0ff20c7f87b19e,0x4e47b19e,0x8ec7b19e,0x5707b19e,0x9f87b19e,0x5a87b19e,0x54eb887b19e,0x4a07b19e,0x8007b19e,0x50c7b19e,0x8f87b19e,0x58c7b19e,0xa007b19e,0x6b07b19e,0x91c7b19e,0x6e87b19e,0xa147b19e,0x70c7b19e,0xaac7b19e,0x8147b19e,0xa4c7b19e,0x8347b19e,0xabc7b19e,0x9507b19e,0xae07b19e],[]),([0x3547b1a7,0x8b87b1a7,0x37c7b1a7,0x9d47b1a7,0x3947b1a7,0xa8c7b1a7,0x3f0801063fcb907b1a7,0x4e47b1a7,0x8ec7b1a7,0x5707b1a7,0x9f87b1a7,0x5a87b1a7,0xa9c7b1a7,0x6907b1a7,0x9007b1a7,0x6947b1a7,0xa047b1a7,0x6987b1a7,0xaa47b1a7,0x6b07b1a7,0x91c7b1a7,0x6e87b1a7,0xa147b1a7,0x70c7b1a7,0xaac7b1a7,0x8147b1a7,0xa4c7b1a7,0x8347b1a7,0xabc7b1a7,0x9507b1a7,0xae07b1a7],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g80 : ∀ q (hq : q < x5s6d0.size), 80 ≤ q → q < 84 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 80 x5s6d0g80c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g84c : List (List ℕ × List ℕ) := [([0x6a0d51ec3f0831fe,0x8822e1ec3f0831fe,0x6f0df1ec3f0831fe,0x8b2751ec3f0831fe,0x718e51ec3f0831fe,0x8daa31ec3f0831fe,0x759391ec3f0831fe,0x88a3b1ec3f0831fe,0x7695c1ec3f0831fe,0x8ba7e1ec3f0831fe,0x7816a1ec3f0831fe,0x8e2a71ec3f0831fe,0x809ac1ec3f0831fe,0x892471ec3f0831fe,0x811ba1ec3f0831fe,0x8c2851ec3f0831fe,0x819c31ec3f0831fe,0x8eaab1ec3f0831fe,0x839df1ec3f0831fe,0x89a511ec3f0831fe,0x841ec1ec3f0831fe,0x8ca8c1ec3f0831fe,0x849f41ec3f0831fe,0x8f2ad1ec3f0831fe,0x85a051ec3f0831fe,0x8d2931ec3f0831fe,0x8620d1ec3f0831fe,0x8faaf1ec3f0831fe,0x8a2541ec3f0831fe,0x902b81ec3f0831fe],[]),([0x3487b205,0x8ac7b205,0x3547b205,0x8b87b205,0x37c7b205,0x9d47b205,0x3947b205,0xa8c7b205,0x7e1062167f87b205,0x4c07b205,0x8cc7b205,0x4e47b205,0x8ec7b205,0x5707b205,0x9f87b205,0x5a87b205,0xa9c7b205,0x6a47b205,0x90c7b205,0x6b07b205,0x91c7b205,0x6e87b205,0xa147b205,0x70c7b205,0xaac7b205,0x80c7b205,0xab87b205,0x7a20640ea4c7b205,0x8347b205,0xabc7b205,0x9507b205,0xae07b205],[]),([0x3547b21f,0x8b87b21f,0x3647b21f,0x8c07b21f,0x37c7b21f,0x9d47b21f,0x3947b21f,0xa8c7b21f,0x7e10621a7f87b21f,0x4e47b21f,0x8ec7b21f,0x5047b21f,0x8f87b21f,0x5707b21f,0x9f87b21f,0x5a87b21f,0xa9c7b21f,0x6b07b21f,0x91c7b21f,0x6c07b21f,0x9247b21f,0x6e87b21f,0xa147b21f,0x70c7b21f,0xaac7b21f,0x8147b21f,0xa4c7b21f,0x8347b21f,0x55eb407b21f,0x8247b21f,0xa507b21f,0x9507b21f,0xae07b21f],[]),([0x3547b225,0x45cb447b225,0x9007b225,0x37c7b225,0x9d47b225,0x3947b225,0xa8c7b225,0x7e10621c7f87b225,0x4e47b225,0x8ec7b225,0x1d85147b225,0x5707b225,0x9f87b225,0x5a87b225,0xa9c7b225,0x6b07b225,0x48eb487b225,0x6e87b225,0xa147b225,0x70c7b225,0xaac7b225,0x8147b225,0xa4c7b225,0x8347b225,0xabc7b225,0x88c7b225,0xa547b225,0x8907b225,0xac07b225,0x9507b225,0xae07b225],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g84 : ∀ q (hq : q < x5s6d0.size), 84 ≤ q → q < 88 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 84 x5s6d0g84c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g88c : List (List ℕ × List ℕ) := [([0x3547b229,0x45cb4c7b229,0x37c7b229,0x9d47b229,0x3947b229,0xa8c7b229,0x7e10621e7f87b229,0x4e47b229,0x8ec7b229,0x1d85147b229,0x5707b229,0x9f87b229,0x5a87b229,0xa9c7b229,0x6b07b229,0x91c7b229,0x1e46d07b229,0x6e87b229,0xa147b229,0x70c7b229,0xaac7b229,0x8147b229,0xa4c7b229,0x8347b229,0xabc7b229,0x89c7b229,0xa587b229,0x8a07b229,0xac47b229,0x9507b229,0xae07b229],[]),([0x1aa3607b22e,0x37c7b22e,0x9d47b22e,0x3947b22e,0xa8c7b22e,0x7e1062207f87b22e,0x2724e87b22e,0x8ec7b22e,0x5307b22e,0x5707b22e,0x9f87b22e,0x5a87b22e,0xa9c7b22e,0x3586b47b22e,0x91c7b22e,0x6d47b22e,0x6e87b22e,0xa147b22e,0x70c7b22e,0xaac7b22e,0x8147b22e,0x526b507b22e,0x8347b22e,0x55eb547b22e,0x8a87b22e,0xa5c7b22e,0x8b07b22e,0xac87b22e,0x9507b22e,0xae07b22e],[]),([0x3547b23b,0x8b87b23b,0x37c7b23b,0x9d47b23b,0x3947b23b,0xa8c7b23b,0x7e1062227f87b23b,0x751392764fc7b23b,0x5707b23b,0x9f87b23b,0x5a87b23b,0xa9c7b23b,0x6b07b23b,0x91c7b23b,0x6d47b23b,0x9447b23b,0x6e87b23b,0xa147b23b,0x70c7b23b,0xaac7b23b,0x8147b23b,0xa4c7b23b,0x8347b23b,0xabc7b23b,0x8c47b23b,0xa687b23b,0x8d87b23b,0xad07b23b,0x9507b23b,0xae07b23b],[]),([0x3547b293,0x45cb507b293,0x37c7b293,0x4eab347b293,0x3887b293,0xa5c7b293,0x3947b293,0xa8c7b293,0x7e1062347f87b293,0x4e47b293,0x8ec7b293,0x5707b293,0x9f87b293,0x1dc5947b293,0xa687b293,0x5a87b293,0xa9c7b293,0x6b07b293,0x91c7b293,0x6e87b293,0xa147b293,0x1e67047b293,0xa707b293,0x70c7b293,0xaac7b293,0x7a20540c81c7b293,0x8347b293,0xabc7b293,0x9507b293,0xae07b293,0xa387b293,0xaf47b293],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g88 : ∀ q (hq : q < x5s6d0.size), 88 ≤ q → q < 92 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 88 x5s6d0g88c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g92c : List (List ℕ × List ℕ) := [([0x3d8921d6,0x754921d6,0x368921d6,0x8bc921d6,0x380921d6,0x9d8921d6,0x394921d6,0xa9c921d6,0x24c7f8921d6,0x24e800921d6,0x4e4921d6,0x8ec921d6,0x570921d6,0x9f8921d6,0x2465a8921d6,0x6b0921d6,0x91c921d6,0x6e8921d6,0xa14921d6,0x70c921d6,0x556b64921d6,0x6cc921d6,0x924921d6,0x6f4921d6,0xa1c921d6,0x814921d6,0xa4c921d6,0x834921d6,0xabc921d6,0x950921d6,0xae0921d6],[]),([0x3d8a6247,0x7a4a6247,0x4e4a6247,0x8b8a6247,0x518a6247,0x9e4a6247,0x520a6247,0xa94a6247,0x29c7f8a6247,0x29e8eca6247,0x2a0944a6247,0x292570a6247,0x9f8a6247,0x2945a8a6247,0xa9ca6247,0xa59ac35c6bca6247,0x6e8a6247,0xa14a6247,0x70ca6247,0xaaca6247,0x814a6247,0xa4ca6247,0x834a6247,0xabca6247,0x904a6247,0xa70a6247,0x910a6247,0xad8a6247,0x950a6247,0xae0a6247],[]),([0x1ec3f4cc2b8,0x7f8cc2b8,0x2724f0cc2b8,0x8eccc2b8,0x570cc2b8,0x4fcb74cc2b8,0x5a8cc2b8,0x54eb78cc2b8,0x644cc2b8,0x574b7ccc2b8,0x484cc2b8,0x7fccc2b8,0x500cc2b8,0x8f0cc2b8,0xa00cc2b8,0xaa0cc2b8,0x6b0cc2b8,0x91ccc2b8,0x6e8cc2b8,0xa14cc2b8,0x70ccc2b8,0xaaccc2b8,0x72ccc2b8,0xaeccc2b8,0x814cc2b8,0xa4ccc2b8,0x834cc2b8,0xabccc2b8,0x854cc2b8,0xaf4cc2b8,0xcba544ac978cc2b8],[]),([0x3d8cf1d6,0x7f8cf1d6,0x248494cf1d6,0x800cf1d6,0x4e4cf1d6,0x8eccf1d6,0x570cf1d6,0x9f8cf1d6,0x5a8cf1d6,0x54eb88cf1d6,0x2504a4cf1d6,0x4b0cf1d6,0x50ccf1d6,0x8f8cf1d6,0x58ccf1d6,0xa00cf1d6,0x6b0cf1d6,0x91ccf1d6,0x6e8cf1d6,0xa14cf1d6,0x70ccf1d6,0x556b64cf1d6,0x6cccf1d6,0x924cf1d6,0x6f4cf1d6,0xa1ccf1d6,0x814cf1d6,0xa4ccf1d6,0x834cf1d6,0xabccf1d6,0x950cf1d6,0xae0cf1d6],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g92 : ∀ q (hq : q < x5s6d0.size), 92 ≤ q → q < 96 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 92 x5s6d0g92c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g96c : List (List ℕ × List ℕ) := [([0x7b0fc1fe418cf1fe,0x4e4cf1fe,0x8eccf1fe,0x570cf1fe,0x9f8cf1fe,0x5a8cf1fe,0x54eb88cf1fe,0x2504a8cf1fe,0x800cf1fe,0x66ccf1fe,0x50ccf1fe,0x8f8cf1fe,0x58ccf1fe,0xa00cf1fe,0x6b0cf1fe,0x91ccf1fe,0x6e8cf1fe,0xa14cf1fe,0x70ccf1fe,0xaaccf1fe,0x77ccf1fe,0x944cf1fe,0x7b0cf1fe,0xa30cf1fe,0x7d0cf1fe,0xab4cf1fe,0x814cf1fe,0xa4ccf1fe,0x834cf1fe,0xabccf1fe,0x950cf1fe,0xae0cf1fe],[]),([0x3d8cf200,0x7f8cf200,0x4e4cf200,0x8eccf200,0x570cf200,0x9f8cf200,0x5a8cf200,0x54eb88cf200,0x2504accf200,0x50ccf200,0x8f8cf200,0x58ccf200,0xa00cf200,0x6b0cf200,0x91ccf200,0x6e8cf200,0xa14cf200,0x70ccf200,0xaaccf200,0x788cf200,0x948cf200,0x7b4cf200,0xa34cf200,0x7d0cf200,0x814cf200,0xa4ccf200,0x834cf200,0xabccf200,0x950cf200,0xae0cf200],[]),([0x3d8cf247,0x7f8cf247,0x4e4cf247,0x8eccf247,0x298534cf247,0x944cf247,0x570cf247,0x9f8cf247,0x5a8cf247,0x54eb88cf247,0x4a0cf247,0x800cf247,0x50ccf247,0x8f8cf247,0x544cf247,0x948cf247,0x58ccf247,0xa00cf247,0xce1ac35c6bccf247,0x6e8cf247,0xa14cf247,0x70ccf247,0xaaccf247,0x814cf247,0xa4ccf247,0x834cf247,0xabccf247,0x904cf247,0xa70cf247,0x910cf247,0xad8cf247,0x950cf247,0xae0cf247],[]),([0x1ec67953ae2,0x3fc67953ae2,0x27267953ae2,0x47667953ae2,0x2b867953ae2,0x4fc67953ae2,0x5a8b616d30a67953ae2,0x25067953ae2,0x40067953ae2,0x28667953ae2,0x47c67953ae2,0x2c667953ae2,0x50067953ae2,0x35867953ae2,0x48e67953ae2,0x37467953ae2,0x50a67953ae2,0x38667953ae2,0x55667953ae2,0x38e67953ae2,0x55a67953ae2,0x40a67953ae2,0x52667953ae2,0x41a67953ae2,0x55e67953ae2,0x42067953ae2,0x56867953ae2,0x4a867953ae2,0x57067953ae2,0x4cc67953ae2,0x57467953ae2],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g96 : ∀ q (hq : q < x5s6d0.size), 96 ≤ q → q < 100 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 96 x5s6d0g96c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g100c : List (List ℕ × List ℕ) := [([0x3d8cf2ab,0x7f8cf2ab,0x4e4cf2ab,0x8eccf2ab,0x570cf2ab,0x9f8cf2ab,0x5a8cf2ab,0x54eb88cf2ab,0x630cf2ab,0xab4cf2ab,0x4a0cf2ab,0x800cf2ab,0x50ccf2ab,0x8f8cf2ab,0x58ccf2ab,0xa00cf2ab,0x668cf2ab,0x6b0cf2ab,0x91ccf2ab,0x6e8cf2ab,0xa14cf2ab,0xce9c338a718cf2ab,0x814cf2ab,0xa4ccf2ab,0x834cf2ab,0xabccf2ab,0x844cf2ab,0xad8cf2ab,0x950cf2ab,0xae0cf2ab,0x99ccf2ab,0xaeccf2ab],[]),([0x7b0fc20c428ff200,0x4e4ff200,0x8ecff200,0x570ff200,0x9f8ff200,0x5a8ff200,0xa9cff200,0x6b0ff200,0x91cff200,0x6e8ff200,0xa14ff200,0x70cff200,0xaacff200,0x77cff200,0x944ff200,0x7b0ff200,0xa30ff200,0x7d0ff200,0xab4ff200,0x788ff200,0x948ff200,0x7b4ff200,0xa34ff200,0x814ff200,0xa4cff200,0x834ff200,0xabcff200,0x950ff200,0xae0ff200],[]),([0x7b0fc20c444ff23b,0x9c93b27c4fcff23b,0x570ff23b,0x9f8ff23b,0x5a8ff23b,0xa9cff23b,0x6b0ff23b,0x91cff23b,0x36a6d8ff23b,0x944ff23b,0x6e8ff23b,0xa14ff23b,0x70cff23b,0xaacff23b,0x3be780ff23b,0x79cff23b,0x7b0ff23b,0xa30ff23b,0x7d0ff23b,0xab4ff23b,0x814ff23b,0xa4cff23b,0x834ff23b,0xabcff23b,0x8c4ff23b,0xa68ff23b,0x8d8ff23b,0xad0ff23b,0x950ff23b,0xae0ff23b],[]),([0x7b0fc20c44cff251,0x4e4ff251,0x8ecff251,0x570ff251,0x9f8ff251,0x5a8ff251,0xa9cff251,0x6b0ff251,0x91cff251,0x6e8ff251,0xa14ff251,0x70cff251,0xaacff251,0x3be784ff251,0x7b0ff251,0xa30ff251,0x7d0ff251,0xab4ff251,0x814ff251,0xa4cff251,0x834ff251,0xabcff251,0x1fb49492cff251,0xa74ff251,0x1fc49a938ff251,0xadcff251,0x950ff251,0xae0ff251],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g100 : ∀ q (hq : q < x5s6d0.size), 100 ≤ q → q < 104 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 100 x5s6d0g100c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
def x5s6d0g104c : List (List ℕ × List ℕ) := [([0x7b0fc20c468ff293,0x4e4ff293,0x8ecff293,0x570ff293,0x9f8ff293,0x594ff293,0xa68ff293,0x5a8ff293,0xa9cff293,0x6b0ff293,0x91cff293,0x6e8ff293,0xa14ff293,0x704ff293,0xa70ff293,0x70cff293,0xaacff293,0x77cff293,0x944ff293,0x7b0ff293,0xa30ff293,0x7c0ff293,0xa74ff293,0x7d0ff293,0xab4ff293,0xfd20540c81cff293,0x834ff293,0xabcff293,0x950ff293,0xae0ff293,0xa38ff293,0xaf4ff293],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0g104 : ∀ q (hq : q < x5s6d0.size), 104 ≤ q → q < 105 → ¬ Reach x5s6d0[q].toFinset 6 0 0xfee8e880 := by
  have check : part x5s6d0 0xfee8e880 6 0 x5s5d0r #[] 104 x5s6d0g104c = true := by decide +kernel
  exact part_ok x5s5d0rok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0ok : correct x5s6d0 6 0 0xfee8e880 := by
  intro q hq
  have lim : q < 105 := hq
  by_cases atMid : q < 52
  ·
    by_cases atMid : q < 24
    ·
      by_cases atMid : q < 12
      ·
        by_cases atMid : q < 4
        ·
          exact x5s6d0g0 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 8
          ·
            exact x5s6d0g4 q hq (by omega) (by omega)
          ·
            exact x5s6d0g8 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 16
        ·
          exact x5s6d0g12 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 20
          ·
            exact x5s6d0g16 q hq (by omega) (by omega)
          ·
            exact x5s6d0g20 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 36
      ·
        by_cases atMid : q < 28
        ·
          exact x5s6d0g24 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 32
          ·
            exact x5s6d0g28 q hq (by omega) (by omega)
          ·
            exact x5s6d0g32 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 44
        ·
          by_cases atMid : q < 40
          ·
            exact x5s6d0g36 q hq (by omega) (by omega)
          ·
            exact x5s6d0g40 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 48
          ·
            exact x5s6d0g44 q hq (by omega) (by omega)
          ·
            exact x5s6d0g48 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 80
    ·
      by_cases atMid : q < 64
      ·
        by_cases atMid : q < 56
        ·
          exact x5s6d0g52 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 60
          ·
            exact x5s6d0g56 q hq (by omega) (by omega)
          ·
            exact x5s6d0g60 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 72
        ·
          by_cases atMid : q < 68
          ·
            exact x5s6d0g64 q hq (by omega) (by omega)
          ·
            exact x5s6d0g68 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 76
          ·
            exact x5s6d0g72 q hq (by omega) (by omega)
          ·
            exact x5s6d0g76 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 92
      ·
        by_cases atMid : q < 84
        ·
          exact x5s6d0g80 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 88
          ·
            exact x5s6d0g84 q hq (by omega) (by omega)
          ·
            exact x5s6d0g88 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 100
        ·
          by_cases atMid : q < 96
          ·
            exact x5s6d0g92 q hq (by omega) (by omega)
          ·
            exact x5s6d0g96 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 104
          ·
            exact x5s6d0g100 q hq (by omega) (by omega)
          ·
            exact x5s6d0g104 q hq (by omega) (by omega)
def x5s6d0r : Array (List Word) := #[[0xaa,0xff,inputA,inputB,inputC,inputD,inputE],[0xaa,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xcc,0xff,inputA,inputB,inputC,inputD,inputE],[0xcc,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xf0,0xff,inputA,inputB,inputC,inputD,inputE],[0xf0,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xff,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xff,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xff,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xff,0xaaaaaa00,inputA,inputB,inputC,inputD,inputE],[0xff,inputA,0xaaaaaaff,inputB,inputC,inputD,inputE],[0xff,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0xff,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0xff,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0xff,inputA,0xcccccc00,inputB,inputC,inputD,inputE],[0xff,inputA,inputB,0xccccccff,inputC,inputD,inputE],[0xff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xff,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0xff,inputA,inputB,0xf0f0f000,inputC,inputD,inputE],[0xff,inputA,inputB,inputC,0xf0f0f0ff,inputD,inputE],[0xff,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xff,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xff,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xff,inputA,inputB,inputC,0xff000000,inputD,0xffffff00],[0xff,inputA,inputB,inputC,0xff000000,inputE,0xffffff00],[0xff,inputA,inputB,inputC,inputD,0xff00ffff,inputE],[0xff,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xff,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0xff,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xff,inputA,inputB,inputC,inputD,inputE,0xffff00ff],[0xff,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xff,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0xff,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0xff,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xff,inputA,inputB,inputC,inputD,inputE,0xffffffaa],[0xff,inputA,inputB,inputC,inputD,inputE,0xffffffcc],[0xff,inputA,inputB,inputC,inputD,inputE,0xfffffff0],[0xff,inputA,inputB,inputC,inputD,0xffff00ff,0xffffff00],[0xff,inputA,inputB,inputC,0xff00ffff,inputE,0xffffff00],[0x8888,0xaaaa,inputA,inputB,inputC,inputD,inputE],[0x8888,0xffff,inputA,inputB,inputC,inputD,inputE],[0x8888,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xa0a0,0xaaaa,inputA,inputB,inputC,inputD,inputE],[0xa0a0,0xffff,inputA,inputB,inputC,inputD,inputE],[0xaa00,0xaaaa,inputA,inputB,inputC,inputD,inputE],[0xaa00,0xffff,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xcccc,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xf0f0,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xff00,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xffff,0xaaaa0000,inputB,inputC,inputD,inputE],[0xaaaa,0xffff,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xffff,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaaaa,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0xaaaa,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xcccceeee,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xccccffff,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xaaaa,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0xaaaa,inputA,inputB,inputC,0xf0f0fafa,inputD,inputE],[0xaaaa,inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[0xaaaa,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xaaaa,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xaaaa,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xaaaa,inputA,inputB,inputC,inputD,0xff00ffaa,inputE],[0xaaaa,inputA,inputB,inputC,inputD,0xff00ffff,inputE],[0xaaaa,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xaaaa,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0xaaaa,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xaaaa,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaa,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0xaaaa,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0xaaaa,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xcccc,0xffff,inputA,inputB,inputC,inputD,inputE],[0xcccc,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xcccc,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xcccc,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xcccc,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xcccc,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xeeee,0xffff,inputA,inputB,inputC,inputD,inputE],[0xeeee,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0,0xffff,inputA,inputB,inputC,inputD,inputE],[0xf0f0,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xf0f0,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xf0f0,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xf0f0,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xff00,0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00,0xffffff,inputA,inputB,inputC,0xff000000,inputE],[0xff00,0xffffff,inputA,inputB,inputC,inputD,inputE],[0xff00,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xff00,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xff00,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xff00,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xff00,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xff00,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffff,0x80808080,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88008800,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88880000,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0xffff,0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffff,0x8888cccc,inputA,inputB,inputC,inputD,inputE],[0xffff,0x8888ffff,inputA,inputB,inputC,inputD,inputE],[0xffff,0xa0a00000,inputA,inputB,inputC,inputD,inputE],[0xffff,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xffff,0xa0a0f0f0,inputA,inputB,inputC,inputD,inputE],[0xffff,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaa000000,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaa00ff00,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputA,inputB,inputC,inputD,0xffffaaaa],[0xffff,0xaaaa0000,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffff,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xffff,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0xffff,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0xffff,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0xffff,inputA,0xcccc8888,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,0xcccceeee,inputC,inputD,inputE],[0xffff,inputA,inputB,0xccccffff,inputC,inputD,inputE],[0xffff,inputA,inputB,0xe0e0e0e0,inputC,inputD,inputE],[0xffff,inputA,inputB,0xee00ee00,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeee0000,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeecccc,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeeffff,inputC,inputD,inputE],[0xffff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xffff,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0xffff,inputA,inputB,0xf0f0a0a0,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,0xf0f0fafa,inputD,inputE],[0xffff,inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[0xffff,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfafaf0f0,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfafaffff,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0xffff,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xffff,inputA,inputB,inputC,0xff00aa00,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,0xff00ffaa,inputE],[0xffff,inputA,inputB,inputC,inputD,0xff00ffff,inputE],[0xffff,inputA,inputB,inputC,inputD,0xff88ff88,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffaaff00,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffaaffff,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffeeffee,inputE],[0xffff,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffff8888],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffeeee],[0xffff,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0xffff,inputA,inputB,inputC,inputD,inputE,0xfffffafa],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffffaa],[0xffff,0xaaaaffff,inputB,inputC,inputD,inputE,0xffffaaaa],[0xf000f,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xf000f,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xf000f,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xaaaaaa,0xffffff,inputA,inputB,inputC,inputD,inputE],[0xaaaaaa,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xcccccc,0xffffff,inputA,inputB,inputC,inputD,inputE],[0xcccccc,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xf0f0f0,0xffffff,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xff0000,0xffffff,inputA,inputB,inputC,0xff000000,inputD],[0xff0000,0xffffff,inputA,inputB,inputC,inputD,inputE],[0xff0000,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xff00ff,0x80808080,inputA,inputB,inputC,inputD,inputE],[0xff00ff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xff00ff,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0xff00ff,0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xff00ff,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xff00ff,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xff00ff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0xff00ff,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xff00ff,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xff00ff,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xffffff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xffffff,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xffffff,0xaa000000,inputA,inputB,inputC,inputD,inputE],[0xffffff,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xffffff,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xffffff,inputA,0xaaffffff,inputB,inputC,inputD,inputE],[0xffffff,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0xffffff,inputA,0xcc000000,inputB,inputC,inputD,inputE],[0xffffff,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0xffffff,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xccffffff,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xf0000000,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xffffff,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0xffffff,inputA,inputB,inputC,0xf0ffffff,inputD,inputE],[0xffffff,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xffffff,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xffffff,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xffffff,inputA,inputB,inputC,0xff000000,inputD,0xffffff00],[0xffffff,inputA,inputB,inputC,0xff000000,inputE,0xffffff00],[0xffffff,inputA,inputB,inputC,inputD,0xffaaaaaa,inputE],[0xffffff,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xffffff,inputA,inputB,inputC,inputD,0xffcccccc,inputE],[0xffffff,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0xffffff,inputA,inputB,inputC,inputD,0xfff0f0f0,inputE],[0xffffff,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xffffff,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffffff,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0xffffff,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0xffffff,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0x1010101,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x1010101,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0x3030303,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0x3030303,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0x5050505,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x5050505,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x5050505,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x7070707,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x7070707,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0xf0f0f0f,0x80808080,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0f0f,0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0f0f,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xfff0fff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xfff0fff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x11111111,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x11111111,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x11111111,0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x11111111,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x11111111,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x11111111,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0x11111111,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0x33333333,0x80808080,inputA,inputB,inputC,inputD,inputE],[0x33333333,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x33333333,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x33333333,0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x33333333,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x33333333,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x33333333,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0x33333333,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x33333333,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0x33333333,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0x55555555,0x80808080,inputA,inputB,inputC,inputD,inputE],[0x55555555,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x55555555,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x55555555,0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x55555555,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x55555555,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x55555555,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0x55555555,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x55555555,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0x55555555,inputA,inputB,inputC,0xfefefefe,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0x57575757,0xa8a8a8a8,inputA,inputB,inputC,inputD,inputE],[0x57575757,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0x5f5f5f5f,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x5f5f5f5f,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x77777777,0x80808080,inputA,inputB,inputC,inputD,inputE],[0x77777777,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x77777777,0x88888888,inputA,0xeeeeeeee,inputC,inputD,inputE],[0x77777777,0x88888888,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x77777777,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x77777777,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x77777777,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x77777777,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0x77777777,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x77777777,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0x7f7f7f7f,0x80808080,inputA,inputB,inputC,inputD,inputE],[0x7f7f7f7f,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x80808080,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88008800,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88880000,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88880000,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0x88888888,0x8888ffff,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xccccffff,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xff000000,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xff00ffff,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xff88ff88,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffff8888],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0x8888cccc,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xa0a00000,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xa0a0f0f0,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xa8a8a8a8,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xaa000000,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xaa000000,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xaa00aa00,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xaa00ff00,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,0xccccffff,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,0xeeeecccc,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,0xfafaf0f0,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,0xff00ffff,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,0xffaaff00,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xaaaaaa00,inputA,inputB,inputC,inputD,inputE,0xffffff00],[inputA,0xaaaaaaff,inputB,inputC,inputD,inputE,0xffffff00],[inputA,0xaaaaffff,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xaaaaffff,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xaaaaffff,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,0xccccffff,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,0xeeeeffff,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,0xf000f000,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,0xf0f0ffff,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,0xfafaffff,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,0xff000000,inputD,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,0xff00ffff,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,0xffaaffff,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,0xaaaaffff,inputB,inputC,inputD,inputE,0xffffff00],[inputA,0xaaffffff,inputB,inputC,0xff000000,inputD,inputE],[inputA,0xc0c0c0c0,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,0xff000000,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE,0xffffff00],[inputA,0xcc000000,inputB,inputC,0xff000000,inputD,inputE],[inputA,0xcc00cc00,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,0xff000000,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE,0xffffff00],[inputA,0xcccc0000,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,0xff000000,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,0xcccc0000,inputB,inputC,inputD,inputE,0xffffff00],[inputA,0xcccc8888,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,0xcccccc00,inputB,inputC,inputD,inputE,0xffffff00],[inputA,inputB,0xccccccff,inputC,inputD,inputE,0xffffff00],[inputA,inputB,0xccccffff,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xccccffff,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,0xccffffff,inputC,0xff000000,inputD,inputE],[inputA,inputB,0xe0e0e0e0,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xee00ee00,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xeeee0000,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,0xeeeeffff,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xf0f0ffff,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xff000000,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xff00ffff,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xffeeffee,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffeeee],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffff00],[inputA,inputB,0xf0000000,inputC,0xff000000,inputD,inputE],[inputA,inputB,0xf000f000,inputC,0xff000000,inputD,inputE],[inputA,inputB,0xf000f000,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,0xf000f000,inputC,inputD,inputE,0xffffff00],[inputA,inputB,0xf0f00000,inputC,0xff000000,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,0xf0f00000,inputC,inputD,inputE,0xffffff00],[inputA,inputB,0xf0f0a0a0,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,0xf0f0f000,inputC,inputD,inputE,0xffffff00],[inputA,inputB,inputC,0xf0f0f0ff,inputD,inputE,0xffffff00],[inputA,inputB,inputC,0xf0f0ffff,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,0xf0ffffff,0xff000000,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,0xff000000,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,0xfafafafa,inputD,inputE,0xffffff00],[inputA,inputB,inputC,0xfcfcfcfc,0xff000000,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE,0xffffff00],[inputA,inputB,inputC,0xff000000,inputD,0xffaaaaaa,inputE],[inputA,inputB,inputC,0xff000000,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,0xff000000,inputD,0xffcccccc,inputE],[inputA,inputB,inputC,0xff000000,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,0xff000000,inputD,0xfff0f0f0,inputE],[inputA,inputB,inputC,0xff000000,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,0xff000000,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,0xff000000,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,0xff000000,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,0xff000000,inputD,inputE,0xffffff00],[inputA,inputB,inputC,0xff00aa00,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,0xff00ffff,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,0xff00ffff,inputE,0xffffff00],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE,0xffffff00],[inputA,inputB,inputC,inputD,0xffccffcc,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,0xffccffcc,inputE,0xffffff00],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE,0xffffff00],[inputA,inputB,inputC,inputD,inputE,0xffff00ff,0xffffff00],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa,0xffffeeee],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa,0xfffffafa],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa,0xffffff00],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa,0xffffffaa],[inputA,inputB,inputC,inputD,inputE,0xffffcccc,0xffffff00],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0,0xffffff00],[inputA,inputB,inputC,inputD,inputE,0xffffff00,0xffffffaa],[inputA,inputB,inputC,inputD,inputE,0xffffff00,0xffffffcc],[inputA,inputB,inputC,inputD,inputE,0xffffff00,0xfffffff0]]
def x5s6d0rg0c : List (ℕ × ℕ) := [(2,0),(3,0),(2,24),(3,24),(2,30),(3,30),(4,0),(4,6),(5,0),(5,1),(6,0),(7,0),(4,48),(5,24),(5,25),(6,24)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg0 : ∀ q (hq : q < x5s6d0r.size), 0 ≤ q → q < 16 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 0 x5s6d0rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg16c : List (ℕ × ℕ) := [(7,24),(8,0),(5,30),(5,31),(6,30),(7,30),(8,6),(8,48),(9,0),(10,0),(10,1),(11,0),(12,0),(12,24),(12,30),(11,1)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg16 : ∀ q (hq : q < x5s6d0r.size), 16 ≤ q → q < 32 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 16 x5s6d0rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg32c : List (ℕ × ℕ) := [(12,1),(12,25),(12,31),(13,0),(14,0),(14,24),(14,30),(15,0),(15,1),(18,0),(19,0),(20,0),(18,6),(19,6),(18,8),(19,8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg32 : ∀ q (hq : q < x5s6d0r.size), 32 ≤ q → q < 48 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 32 x5s6d0rg32c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg48c : List (ℕ × ℕ) := [(21,0),(21,6),(21,8),(22,0),(23,0),(24,0),(27,0),(27,6),(27,8),(28,0),(29,0),(30,0),(30,2),(31,0),(32,0),(33,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg48 : ∀ q (hq : q < x5s6d0r.size), 48 ≤ q → q < 64 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 48 x5s6d0rg48c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg64c : List (ℕ × ℕ) := [(34,0),(30,12),(31,6),(32,6),(33,6),(34,6),(35,0),(31,8),(32,8),(33,8),(34,8),(35,2),(35,12),(36,0),(37,0),(37,6)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg64 : ∀ q (hq : q < x5s6d0r.size), 64 ≤ q → q < 80 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 64 x5s6d0rg64c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg80c : List (ℕ × ℕ) := [(37,8),(23,24),(27,24),(31,24),(33,24),(34,24),(37,24),(38,0),(39,0),(23,30),(30,30),(31,30),(33,30),(35,30),(37,30),(23,32)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg80 : ∀ q (hq : q < x5s6d0r.size), 80 ≤ q → q < 96 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 80 x5s6d0rg80c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg96c : List (ℕ × ℕ) := [(25,32),(26,32),(30,32),(31,32),(33,32),(35,32),(28,32),(37,32),(40,0),(40,2),(41,0),(42,0),(43,0),(43,24),(44,24),(45,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg96 : ∀ q (hq : q < x5s6d0r.size), 96 ≤ q → q < 112 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 96 x5s6d0rg96c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg112c : List (ℕ × ℕ) := [(41,6),(42,6),(44,30),(46,0),(41,8),(42,8),(44,32),(47,0),(48,0),(49,0),(52,0),(42,48),(42,50),(47,24),(50,24),(51,24)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg112 : ∀ q (hq : q < x5s6d0r.size), 112 ≤ q → q < 128 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 112 x5s6d0rg112c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg128c : List (ℕ × ℕ) := [(52,24),(46,30),(46,32),(54,0),(55,24),(56,0),(57,0),(42,60),(47,30),(50,30),(51,30),(52,30),(53,30),(55,30),(56,6),(57,6)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg128 : ∀ q (hq : q < x5s6d0r.size), 128 ≤ q → q < 144 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 128 x5s6d0rg128c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg144c : List (ℕ × ℕ) := [(56,48),(58,0),(47,32),(50,32),(51,32),(52,32),(53,32),(55,32),(56,8),(57,8),(56,50),(58,2),(56,60),(59,0),(60,0),(60,24)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg144 : ∀ q (hq : q < x5s6d0r.size), 144 ≤ q → q < 160 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 144 x5s6d0rg144c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg160c : List (ℕ × ℕ) := [(61,0),(60,30),(61,6),(60,32),(61,8),(62,72),(4,3),(8,3),(13,3),(65,0),(66,0),(65,24),(66,24),(65,30),(66,30),(25,33)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg160 : ∀ q (hq : q < x5s6d0r.size), 160 ≤ q → q < 176 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 160 x5s6d0rg160c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg176c : List (ℕ × ℕ) := [(26,33),(28,33),(40,1),(42,1),(43,1),(43,25),(42,7),(46,1),(56,1),(47,31),(53,31),(56,7),(56,49),(58,1),(60,31),(67,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg176 : ∀ q (hq : q < x5s6d0r.size), 176 ≤ q → q < 192 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 176 x5s6d0rg176c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg192c : List (ℕ × ℕ) := [(67,6),(68,0),(69,0),(69,1),(70,0),(67,48),(68,24),(69,24),(69,25),(70,24),(71,0),(68,30),(69,30),(69,31),(70,30),(71,6)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg192 : ∀ q (hq : q < x5s6d0r.size), 192 ≤ q → q < 208 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 192 x5s6d0rg192c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg208c : List (ℕ × ℕ) := [(71,48),(72,0),(73,0),(73,1),(74,0),(75,0),(74,24),(75,24),(74,30),(75,30),(75,1),(75,25),(75,31),(76,0),(0,64),(1,64)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg208 : ∀ q (hq : q < x5s6d0r.size), 208 ≤ q → q < 224 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 208 x5s6d0rg208c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg224c : List (ℕ × ℕ) := [(6,16),(13,16),(5,76),(12,76),(13,76),(16,64),(17,64),(41,4),(42,4),(43,4),(43,28),(47,4),(50,4),(56,4),(47,34),(59,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg224 : ∀ q (hq : q < x5s6d0r.size), 224 ≤ q → q < 240 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 224 x5s6d0rg224c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg240c : List (ℕ × ℕ) := [(60,4),(60,28),(61,4),(60,34),(67,3),(72,3),(9,90),(10,90),(10,114),(13,90),(12,90),(14,90),(8,90),(41,18),(47,18),(48,18)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg240 : ∀ q (hq : q < x5s6d0r.size), 240 ≤ q → q < 256 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 240 x5s6d0rg240c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg256c : List (ℕ × ℕ) := [(49,18),(42,18),(50,18),(60,18),(42,66),(55,42),(56,18),(60,42),(61,18),(56,66),(41,96),(47,96),(49,96),(48,96),(47,102),(54,96)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg256 : ∀ q (hq : q < x5s6d0r.size), 256 ≤ q → q < 272 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 256 x5s6d0rg256c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg272c : List (ℕ × ℕ) := [(60,96),(42,108),(55,102),(60,102),(56,96),(61,96),(56,108),(63,112),(64,112),(69,76),(72,76),(68,90),(72,90),(73,90),(73,114),(69,90)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg272 : ∀ q (hq : q < x5s6d0r.size), 272 ≤ q → q < 288 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 272 x5s6d0rg272c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg288c : List (ℕ × ℕ) := [(76,90),(67,90),(74,90),(75,90),(71,90),(77,64),(78,64),(79,0),(79,2),(79,3),(79,9),(80,0),(81,0),(81,2),(81,3),(82,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg288 : ∀ q (hq : q < x5s6d0r.size), 288 ≤ q → q < 304 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 288 x5s6d0rg288c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg304c : List (ℕ × ℕ) := [(81,24),(81,26),(81,27),(82,24),(84,0),(85,0),(85,1),(86,0),(89,0),(90,0),(90,24),(85,4),(86,2),(89,2),(90,2),(90,26)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg304 : ∀ q (hq : q < x5s6d0r.size), 304 ≤ q → q < 320 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 304 x5s6d0rg304c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg320c : List (ℕ × ℕ) := [(91,0),(89,3),(90,3),(90,27),(91,1),(91,4),(92,24),(79,15),(81,13),(82,6),(90,6),(85,18),(90,13),(91,18),(92,30),(93,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg320 : ∀ q (hq : q < x5s6d0r.size), 320 ≤ q → q < 336 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 320 x5s6d0rg320c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg336c : List (ℕ × ℕ) := [(79,17),(79,64),(81,16),(82,8),(90,8),(81,40),(90,16),(90,40),(92,32),(83,9),(85,9),(85,11),(81,33),(87,9),(89,9),(90,9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg336 : ∀ q (hq : q < x5s6d0r.size), 336 ≤ q → q < 352 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 336 x5s6d0rg336c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg352c : List (ℕ × ℕ) := [(85,21),(81,39),(87,15),(89,15),(90,15),(91,9),(81,41),(87,17),(89,17),(90,17),(91,11),(91,21),(84,9),(90,33),(90,39),(90,41)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg352 : ∀ q (hq : q < x5s6d0r.size), 352 ≤ q → q < 368 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 352 x5s6d0rg352c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg368c : List (ℕ × ℕ) := [(93,16),(94,0),(86,48),(86,50),(87,51),(95,0),(96,0),(97,0),(86,60),(87,61),(95,6),(96,6),(97,6),(98,0),(87,64),(95,8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg368 : ∀ q (hq : q < x5s6d0r.size), 368 ≤ q → q < 384 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 368 x5s6d0rg368c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg384c : List (ℕ × ℕ) := [(96,8),(97,8),(98,2),(98,12),(99,0),(100,0),(100,6),(100,8),(88,64),(90,48),(85,96),(91,49),(91,96),(79,88),(90,50),(81,82)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg384 : ∀ q (hq : q < x5s6d0r.size), 384 ≤ q → q < 400 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 384 x5s6d0rg384c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg400c : List (ℕ × ℕ) := [(91,52),(90,82),(90,51),(81,83),(90,57),(90,83),(93,27),(93,76),(94,24),(96,24),(100,24),(88,88),(93,30),(93,32),(93,33),(101,0)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg400 : ∀ q (hq : q < x5s6d0r.size), 400 ≤ q → q < 416 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 400 x5s6d0rg400c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg416c : List (ℕ × ℕ) := [(91,60),(91,61),(98,30),(102,0),(102,24),(103,0),(91,64),(98,32),(102,2),(102,26),(103,2),(104,0),(102,3),(102,27),(103,3),(104,1)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg416 : ∀ q (hq : q < x5s6d0r.size), 416 ≤ q → q < 432 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 416 x5s6d0rg416c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg432c : List (ℕ × ℕ) := [(104,4),(79,94),(81,92),(91,66),(90,92),(81,93),(90,63),(90,93),(93,37),(93,90),(94,30),(100,30),(88,94),(91,70),(102,13),(104,18)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg432 : ∀ q (hq : q < x5s6d0r.size), 432 ≤ q → q < 448 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 432 x5s6d0rg432c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg448c : List (ℕ × ℕ) := [(91,112),(104,9),(104,96),(89,64),(90,64),(89,88),(90,88),(89,94),(90,94),(90,65),(90,89),(90,95),(84,64),(93,40),(100,32),(99,32)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg448 : ∀ q (hq : q < x5s6d0r.size), 448 ≤ q → q < 464 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 448 x5s6d0rg448c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg464c : List (ℕ × ℕ) := [(102,16),(102,40),(104,11),(102,82),(104,21),(102,92),(99,33),(102,33),(103,9),(102,39),(103,15),(102,41),(103,17),(102,83),(102,93),(103,64)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg464 : ∀ q (hq : q < x5s6d0r.size), 464 ≤ q → q < 480 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 464 x5s6d0rg464c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
def x5s6d0rg480c : List (ℕ × ℕ) := [(103,88),(103,94)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rg480 : ∀ q (hq : q < x5s6d0r.size), 480 ≤ q → q < 482 → ¬ Reach x5s6d0r[q].toFinset 6 0 0xfee8e880 := by
  have check : aliasPart x5s6d0r x5s6d0 0xfee8e880 x5maps 480 x5s6d0rg480c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d0rok : correct x5s6d0r 6 0 0xfee8e880 := by
  intro q hq
  have lim : q < 482 := hq
  by_cases atMid : q < 240
  ·
    by_cases atMid : q < 112
    ·
      by_cases atMid : q < 48
      ·
        by_cases atMid : q < 16
        ·
          exact x5s6d0rg0 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 32
          ·
            exact x5s6d0rg16 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg32 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 80
        ·
          by_cases atMid : q < 64
          ·
            exact x5s6d0rg48 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg64 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 96
          ·
            exact x5s6d0rg80 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg96 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 176
      ·
        by_cases atMid : q < 144
        ·
          by_cases atMid : q < 128
          ·
            exact x5s6d0rg112 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg128 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 160
          ·
            exact x5s6d0rg144 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg160 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 208
        ·
          by_cases atMid : q < 192
          ·
            exact x5s6d0rg176 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg192 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 224
          ·
            exact x5s6d0rg208 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg224 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 368
    ·
      by_cases atMid : q < 304
      ·
        by_cases atMid : q < 272
        ·
          by_cases atMid : q < 256
          ·
            exact x5s6d0rg240 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg256 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 288
          ·
            exact x5s6d0rg272 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg288 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 336
        ·
          by_cases atMid : q < 320
          ·
            exact x5s6d0rg304 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg320 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 352
          ·
            exact x5s6d0rg336 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg352 q hq (by omega) (by omega)
    ·
      by_cases atMid : q < 432
      ·
        by_cases atMid : q < 400
        ·
          by_cases atMid : q < 384
          ·
            exact x5s6d0rg368 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg384 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 416
          ·
            exact x5s6d0rg400 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg416 q hq (by omega) (by omega)
      ·
        by_cases atMid : q < 464
        ·
          by_cases atMid : q < 448
          ·
            exact x5s6d0rg432 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg448 q hq (by omega) (by omega)
        ·
          by_cases atMid : q < 480
          ·
            exact x5s6d0rg464 q hq (by omega) (by omega)
          ·
            exact x5s6d0rg480 q hq (by omega) (by omega)
def x5s6d1 : Array (List Word) := #[[0x80808080,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xa8a8a8a8,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE]]
def x5s6d1g0c : List (List ℕ × List ℕ) := [([0x1813,0x502a1c401813,0x401813,0x40281f801813,0xc18801813,0x2001813,0x1c801813,0x2c01813,0x1fc01813,0x101703616401813,0xcc01813,0x19801813,0x10401813,0x1d401813,0x10c01813,0x20801813,0x11401813,0x1a801813,0x12c01813,0x1d801813,0x13401813,0x20c01813,0x16c01813,0x1e401813,0x17801813,0x21801813,0x1c001813,0x22c01813],[0x49493127,0x46c8e127,0x42885927,0x3f47f127,0x39c74127,0x2c859927,0x1a035927]),([0xc09833,0xf409833,0x6818809833,0x2009833,0x1c809833,0x2c09833,0x1fc09833,0x2c14809833,0xc409833,0x1cc09833,0xc809833,0x20009833,0x681703616409833,0x603506e19809833,0x10409833,0x1d409833,0x10c09833,0x20809833,0x11409833,0x1a809833,0x12c09833,0x1d809833,0x13409833,0x20c09833,0x16c09833,0x1e409833,0x17809833,0x21809833,0x1c009833,0x22c09833],[0x4708f92c,0x4648d12c,0x42c8712c,0x3f88092c,0x3a07592c,0x2cc5b12c,0x1ac3892c]),([0x100302605c0d859,0x1086202605c0d859,0x380802605c0d859,0x1307202605c0d859,0x500b02605c0d859,0x1587f02605c0d859,0x683302605c0d859,0x1106602605c0d859,0x704102605c0d859,0x1387502605c0d859,0x804302605c0d859,0x1608202605c0d859,0xc04502605c0d859,0x1186a02605c0d859,0xc84b02605c0d859,0x1407602605c0d859,0xd04d02605c0d859,0x1688302605c0d859,0xe04e02605c0d859,0x1206f02605c0d859,0xe85302605c0d859,0x1487702605c0d859,0xf05502605c0d859,0x1708402605c0d859,0xf85b02605c0d859,0x1507902605c0d859,0x1005e02605c0d859,0x1788602605c0d859,0x1287002605c0d859,0x1808b02605c0d859],[0x11c23a47890134,0x10b21843488134,0xfe1fe40081934,0xf61ee3e07c934,0xe81d23a876934,0xb31682d45c134,0x6b0d81b442934]),([0x985b,0x1800985b,0xc0985b,0x1880985b,0x200985b,0x1c80985b,0x2c0985b,0x1fc0985b,0xb81b03e1640985b,0xc40985b,0x1900985b,0xcc0985b,0x1980985b,0x1040985b,0x1d40985b,0x10c0985b,0x2080985b,0x1100985b,0x1a00985b,0x1140985b,0x1a80985b,0x12c0985b,0x1d80985b,0x1340985b,0x20c0985b,0x1680985b,0x2140985b,0x905c0ba1e40985b,0x1780985b,0x2180985b,0x1c00985b,0x22c0985b],[0x47090935,0x42c88935,0x3f882135,0x3d07a935,0x3a077135,0x2cc5c935,0x1ac43935])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1g0 : ∀ q (hq : q < x5s6d1.size), 0 ≤ q → q < 4 → ¬ Reach x5s6d1[q].toFinset 6 1 0xfee8e880 := by
  have check : part x5s6d1 0xfee8e880 6 1 x5s5d1r x5s6d0r 0 x5s6d1g0c = true := by decide +kernel
  exact part_ok x5s5d1rok x5s6d0rok check
def x5s6d1g4c : List (List ℕ × List ℕ) := [([0x601809862,0x2009862,0x1c809862,0x2c09862,0x1fc09862,0xb81b04216409862,0x660d009862,0x19809862,0xf409862,0x10409862,0x1d409862,0x10c09862,0x20809862,0x8a11809862,0x1a809862,0x12409862,0x12c09862,0x1d809862,0x13409862,0x20c09862,0x16c09862,0xf223809862,0x17809862,0x10c23c09862,0x17c09862,0x1e809862,0x18409862,0x21c09862,0x1c009862,0x22c09862],[0x47091138,0x42c89138,0x3f882938,0x3a077938,0x39473138,0x2cc5d138,0x1ac46138]),([0xc09866,0x18809866,0x2009866,0x1c809866,0x2c09866,0x1fc09866,0xb81b04416409866,0x603306a0dc09866,0x10409866,0x1d409866,0x10c09866,0x20809866,0x11409866,0x1a809866,0x12409866,0x1bc09866,0x12c09866,0x1d809866,0x13409866,0x20c09866,0x16c09866,0x1e409866,0x17809866,0x21809866,0x18c09866,0x1ec09866,0x19409866,0x22009866,0x1c009866,0x22c09866],[0x47091939,0x42c89939,0x3f883139,0x3a078139,0x38872139,0x2cc5d939,0x1ac47139]),([0xc09879,0xc423809879,0x2009879,0xe423409879,0x2409879,0x1e809879,0x2c09879,0x1fc09879,0xb81b05416409879,0xcc09879,0x19809879,0x10409879,0x1d409879,0x1e10809879,0x1ec09879,0x10c09879,0x20809879,0x11409879,0x1a809879,0x12c09879,0x1d809879,0x2213009879,0x1f009879,0x13409879,0x20c09879,0x905b0b817409879,0x17809879,0x21809879,0x1c009879,0x22c09879,0x1e009879,0x23009879],[0x47092140,0x42c8b140,0x3f884940,0x3a079940,0x2cc5f140,0x29854140,0x1ac4e140]),([0x4c1e86a,0x1481e86a,0xcc1e86a,0x1881e86a,0xe01e86a,0x1d01e86a,0xe41e86a,0x2041e86a,0x7c1641e86a,0x7e1981e86a,0x801bc1e86a,0x741041e86a,0x1d41e86a,0x7610c1e86a,0x2081e86a,0x1e04508e1201e86a,0x12c1e86a,0x1d81e86a,0x1341e86a,0x20c1e86a,0x16c1e86a,0x1e41e86a,0x1781e86a,0x2181e86a,0x19c1e86a,0x1f01e86a,0x1a41e86a,0x2241e86a,0x1c01e86a,0x22c1e86a],[0x45c8c14f,0x43c8a14f,0x4088394f,0x3b07894f,0x3807094f,0x2dc5e14f,0x1cc4814f])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1g4 : ∀ q (hq : q < x5s6d1.size), 4 ≤ q → q < 8 → ¬ Reach x5s6d1[q].toFinset 6 1 0xfee8e880 := by
  have check : part x5s6d1 0xfee8e880 6 1 x5s5d1r x5s6d0r 4 x5s6d1g4c = true := by decide +kernel
  exact part_ok x5s5d1rok x5s6d0rok check
def x5s6d1g8c : List (List ℕ × List ℕ) := [([0x98170360882c866,0x1983506c0dc2c866,0x1042c866,0x1d42c866,0x10c2c866,0x2082c866,0x1142c866,0x1a82c866,0x921282c866,0x1bc2c866,0x12c2c866,0x1d82c866,0x1342c866,0x20c2c866,0x9c13c2c866,0x1442c866,0x14c2c866,0x1dc2c866,0x1542c866,0x2102c866,0x16c2c866,0x1e42c866,0x1782c866,0x2182c866,0x18c2c866,0x1ec2c866,0x1942c866,0x2202c866,0x1c02c866,0x22c2c866],[0x440899a3,0x40c831a3,0x3e47d1a3,0x3b4781a3,0x38c721a3,0x2e05d9a3,0x214471a3]),([0x98170360902c86f,0xcc2c86f,0x1982c86f,0x1042c86f,0x1d42c86f,0x10c2c86f,0x2082c86f,0x1142c86f,0x1a82c86f,0x12c2c86f,0x1d82c86f,0x1342c86f,0x20c2c86f,0x9c1402c86f,0x14c2c86f,0x1dc2c86f,0x1542c86f,0x2102c86f,0x16c2c86f,0x1e42c86f,0x1782c86f,0x2182c86f,0x570d61b02c86f,0x1f42c86f,0x580da1b82c86f,0x2282c86f,0x1c02c86f,0x22c2c86f],[0x4408a9a5,0x40c841a5,0x3e47d9a5,0x3b4791a5,0x3786f9a5,0x2e05e9a5,0x214489a5]),([0x98170360a82c879,0xcc2c879,0x1982c879,0x1042c879,0x1d42c879,0x1082c879,0x1ec2c879,0x10c2c879,0x2082c879,0x1142c879,0x1a82c879,0x12c2c879,0x1d82c879,0x1302c879,0x1f02c879,0x1342c879,0x20c2c879,0x1382c879,0x1bc2c879,0x14c2c879,0x1dc2c879,0x1502c879,0x1f42c879,0x1542c879,0x2102c879,0x2b05b0b81742c879,0x1782c879,0x2182c879,0x1c02c879,0x22c2c879,0x1e02c879,0x2302c879],[0x4408b1ab,0x40c849ab,0x3e47e1ab,0x3b4799ab,0x2e05f1ab,0x29c541ab,0x2144e1ab])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1g8 : ∀ q (hq : q < x5s6d1.size), 8 ≤ q → q < 11 → ¬ Reach x5s6d1[q].toFinset 6 1 0xfee8e880 := by
  have check : part x5s6d1 0xfee8e880 6 1 x5s5d1r x5s6d0r 8 x5s6d1g8c = true := by decide +kernel
  exact part_ok x5s5d1rok x5s6d0rok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1ok : correct x5s6d1 6 1 0xfee8e880 := by
  intro q hq
  have lim : q < 11 := hq
  by_cases atMid : q < 4
  ·
    exact x5s6d1g0 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 8
    ·
      exact x5s6d1g4 q hq (by omega) (by omega)
    ·
      exact x5s6d1g8 q hq (by omega) (by omega)
def x5s6d1r : Array (List Word) := #[[0x80808080,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88008800,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88880000,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0x88888888,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0x88888888,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0x88888888,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xf8f8f8f8,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0x88888888,inputA,inputB,inputC,0xff000000,inputD,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xff88ff88,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0x88888888,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffff8888],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0x88888888,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xa0a0a0a0,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xe0e0e0e0,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xee00ee00,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xeeee0000,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xfefefefe,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,0xff000000,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xffeeffee,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffeeee],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE,0xffffff00]]
def x5s6d1rg0c : List (ℕ × ℕ) := [(0,0),(0,2),(0,3),(1,0),(1,2),(1,3),(1,24),(1,26),(1,27),(2,0),(3,0),(3,1),(4,0),(5,0),(5,24),(3,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1rg0 : ∀ q (hq : q < x5s6d1r.size), 0 ≤ q → q < 16 → ¬ Reach x5s6d1r[q].toFinset 6 1 0xfee8e880 := by
  have check : aliasPart x5s6d1r x5s6d1 0xfee8e880 x5maps 0 x5s6d1rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d1ok check
def x5s6d1rg16c : List (ℕ × ℕ) := [(4,2),(5,2),(5,26),(6,0),(4,3),(5,3),(5,27),(6,1),(6,4),(5,6),(5,8),(5,9),(5,48),(5,50),(5,51),(7,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1rg16 : ∀ q (hq : q < x5s6d1r.size), 16 ≤ q → q < 32 → ¬ Reach x5s6d1r[q].toFinset 6 1 0xfee8e880 := by
  have check : aliasPart x5s6d1r x5s6d1 0xfee8e880 x5maps 16 x5s6d1rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d1ok check
def x5s6d1rg32c : List (ℕ × ℕ) := [(7,32),(7,33),(6,60),(6,61),(8,0),(8,24),(9,0),(6,64),(8,2),(8,26),(9,2),(10,0),(8,3),(8,27),(9,3),(10,1)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1rg32 : ∀ q (hq : q < x5s6d1r.size), 32 ≤ q → q < 48 → ¬ Reach x5s6d1r[q].toFinset 6 1 0xfee8e880 := by
  have check : aliasPart x5s6d1r x5s6d1 0xfee8e880 x5maps 32 x5s6d1rg32c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d1ok check
def x5s6d1rg48c : List (ℕ × ℕ) := [(10,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1rg48 : ∀ q (hq : q < x5s6d1r.size), 48 ≤ q → q < 49 → ¬ Reach x5s6d1r[q].toFinset 6 1 0xfee8e880 := by
  have check : aliasPart x5s6d1r x5s6d1 0xfee8e880 x5maps 48 x5s6d1rg48c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s6d1ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s6d1rok : correct x5s6d1r 6 1 0xfee8e880 := by
  intro q hq
  have lim : q < 49 := hq
  by_cases atMid : q < 32
  ·
    by_cases atMid : q < 16
    ·
      exact x5s6d1rg0 q hq (by omega) (by omega)
    ·
      exact x5s6d1rg16 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 48
    ·
      exact x5s6d1rg32 q hq (by omega) (by omega)
    ·
      exact x5s6d1rg48 q hq (by omega) (by omega)
def x5s7d0 : Array (List Word) := #[[0xff,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xaaaa,0xffff,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xffff,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffffff,inputA,inputB,inputC,0xff000000,inputD,inputE]]
def x5s7d0g0c : List (List ℕ × List ℕ) := [([0x823,0x2cb8823,0x801823,0x40cc023,0x1002823,0x54dd023,0x360a0e7823,0x3e09ceb023,0x18a2823,0x44d8023,0x1ca6823,0x58df823,0x20ab823,0x70e8823,0x24b7823,0x80ed823,0x28b8023,0x90ef823,0x30c6023,0x5ce1023,0x34c8823,0x74e9823,0x38ca823,0x84ee823,0x3ccb823,0x94f0023,0x48da023,0x78ea823,0x4cdb823,0x88ef023,0x50dc823,0x98f0823,0x18032068e6023],[]),([0xa415034,0xf83f834,0xb016834,0x10c45034,0xb817834,0x1204a034,0x1344f034,0x6a0e83d034,0xc028834,0xfc40034,0xc42c834,0x11045834,0xc82f834,0x1244a834,0xd835834,0x10042834,0xdc38834,0x11447034,0xe03a834,0x1284c034,0x660e43b834,0xec3d834,0x11848034,0xf03e034,0x12c4d034,0xf43e834,0x1384f834,0x10443834,0x1304e034,0x10844034,0x13c50834,0x11c49034,0x14051834],[]),([0xa81586b,0x1bc9586b,0xd01b06b,0x1e89786b,0x1442906b,0x2009986b,0x1642d06b,0x22c9b86b,0x17c3106b,0x2549e06b,0x1a09386b,0x2309c06b,0x1a49406b,0x2589e86b,0x1a89486b,0x274a086b,0x6c0da2149a06b,0x1c49606b,0x2389c86b,0x1d49686b,0x2609f06b,0x1dc9706b,0x278a106b,0x1ec9806b,0x2409d06b,0x1f09886b,0x2689f86b,0x1f49906b,0x27ca186b,0x21c9a86b,0x270a006b,0x2209b06b,0x284a206b,0x2489d86b,0x28ca286b],[]),([0x1e8ac877,0x660d01c877,0x14429877,0x200ae877,0x1642d877,0x22cb1077,0x17c31877,0x254b3877,0x1a895077,0x210af077,0x1c0a3877,0x234b1877,0x1d0a8077,0x25cb4077,0x1ac97077,0x214af877,0x1c4a4077,0x238b2077,0x1d4a9077,0x260b4877,0x780f2278b6077,0x1ecad077,0x240b2877,0x1f0ad877,0x268b5077,0x1f4ae077,0x27cb6877,0x21cb0077,0x270b5877,0x220b0877,0x284b7077,0x248b3077,0x28cb7877],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d0g0 : ∀ q (hq : q < x5s7d0.size), 0 ≤ q → q < 4 → ¬ Reach x5s7d0[q].toFinset 7 0 0xfee8e880 := by
  have check : part x5s7d0 0xfee8e880 7 0 x5s6d0r #[] 0 x5s7d0g0c = true := by decide +kernel
  exact part_ok x5s6d0rok (noRows _ _ _) check
def x5s7d0g4c : List (List ℕ × List ℕ) := [([0x680d41d07a,0x1442a07a,0x200ba87a,0x1642e07a,0x22cbd07a,0x17c3207a,0x254bf87a,0x1ac9787a,0x214bb07a,0x1c4a487a,0x238bd87a,0x1d4a987a,0x260c007a,0x1dcac87a,0x13c294c207a,0x1b8a307a,0x218bb87a,0x1c8a707a,0x23cbe07a,0x1d8ac07a,0x264c087a,0x1ecb907a,0x240be87a,0x1f0b987a,0x268c107a,0x1f4ba07a,0x27cc287a,0x21cbc07a,0x270c187a,0x220bc87a,0x284c307a,0x248bf07a,0x28cc387a],[]),([0xd020085,0x1e8bb085,0x1442a885,0x200cc885,0x15c2c085,0x218cf885,0x1642e885,0x22cd1085,0x17c32885,0x254d3885,0x6b0d81b49a085,0x1c4a5085,0x238d1885,0x1d4aa085,0x260d4085,0x1dcaf885,0x278d6085,0x1ecc4885,0x240d2085,0x1f0c7085,0x268d4885,0x1f4c9085,0x27cd6885,0x204ce085,0x244d2885,0x208ce885,0x26cd5085,0x20ccf085,0x280d7085,0x21cd0085,0x270d5885,0x220d0885,0x284d7885,0x248d3085,0x28cd8085],[]),([0xd02689e,0xf4294c209e,0x1442b09e,0x200cd09e,0x1642f09e,0x22cdd89e,0x17c3389e,0x254e709e,0x1aca109e,0x214d609e,0x1c4a609e,0x238df09e,0x1d4ab09e,0x260e809e,0x770f01e4b609e,0x1ecc589e,0x240e089e,0x1f0c809e,0x268e909e,0x1f4ca09e,0x27ceb89e,0x1f8cb09e,0x280ec09e,0x21cd989e,0x270ea09e,0x220db09e,0x284ec89e,0x224dc09e,0x288ed09e,0x248e489e,0x28ced89e,0x24ce689e,0x290ee09e],[]),([0x2a4550d1,0x310c40d1,0x2ac560d1,0x324cd8d1,0x2b4570d1,0x338de0d1,0xc0184330d1,0x15e2c0588d1,0x2fc9d8d1,0x328d30d1,0x300a58d1,0x33cde8d1,0x304a88d1,0x350e18d1,0x308aa8d1,0x354e20d1,0x30cb30d1,0x368e48d1,0x314c50d1,0x340e00d1,0x318c68d1,0x358e28d1,0x31cc78d1,0x35ce30d1,0x320c98d1,0x36ce50d1,0x32cd88d1,0x360e38d1,0x330d90d1,0x364e40d1,0x334da8d1,0x370e58d1,0xd21a6374e60d1],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d0g4 : ∀ q (hq : q < x5s7d0.size), 4 ≤ q → q < 8 → ¬ Reach x5s7d0[q].toFinset 7 0 0xfee8e880 := by
  have check : part x5s7d0 0xfee8e880 7 0 x5s6d0r #[] 4 x5s7d0g4c = true := by decide +kernel
  exact part_ok x5s6d0rok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d0ok : correct x5s7d0 7 0 0xfee8e880 := by
  intro q hq
  have lim : q < 8 := hq
  by_cases atMid : q < 4
  ·
    exact x5s7d0g0 q hq (by omega) (by omega)
  ·
    exact x5s7d0g4 q hq (by omega) (by omega)
def x5s7d0r : Array (List Word) := #[[0xaaaa,0xffff,inputA,inputB,inputC,inputD,inputE],[0xcccc,0xffff,inputA,inputB,inputC,inputD,inputE],[0xf0f0,0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00,0xffff,inputA,inputB,inputC,inputD,inputE],[0xffff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xffff,0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xffff,0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[0xffff,inputA,0xaaaaffff,inputB,inputC,inputD,inputE],[0xffff,inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[0xffff,inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[0xffff,inputA,0xcccc0000,inputB,inputC,inputD,inputE],[0xffff,inputA,inputB,0xccccffff,inputC,inputD,inputE],[0xffff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xffff,inputA,inputB,0xf000f000,inputC,inputD,inputE],[0xffff,inputA,inputB,0xf0f00000,inputC,inputD,inputE],[0xffff,inputA,inputB,inputC,0xf0f0ffff,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfafafafa,inputD,inputE],[0xffff,inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[0xffff,inputA,inputB,inputC,0xff000000,inputD,inputE],[0xffff,inputA,inputB,inputC,inputD,0xff00ffff,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[0xffff,inputA,inputB,inputC,inputD,0xffccffcc,inputE],[0xffff,inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffcccc],[0xffff,inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[0xffff,inputA,inputB,inputC,inputD,inputE,0xffffff00],[0xff00ff,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0xf0f0f0f,0x88888888,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x11111111,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x33333333,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x55555555,0x88888888,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[0x77777777,0x88888888,inputA,inputB,inputC,inputD,inputE]]
def x5s7d0rg0c : List (ℕ × ℕ) := [(1,0),(1,24),(1,30),(1,32),(2,0),(2,6),(2,8),(3,0),(4,0),(2,48),(2,50),(3,24),(4,24),(5,0),(2,60),(3,30)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d0rg0 : ∀ q (hq : q < x5s7d0r.size), 0 ≤ q → q < 16 → ¬ Reach x5s7d0r[q].toFinset 7 0 0xfee8e880 := by
  have check : aliasPart x5s7d0r x5s7d0 0xfee8e880 x5maps 0 x5s7d0rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s7d0ok check
def x5s7d0rg16c : List (ℕ × ℕ) := [(4,30),(5,6),(5,48),(3,32),(4,32),(5,8),(5,50),(5,60),(6,0),(6,24),(6,30),(6,32),(2,1),(5,1),(2,4),(5,4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d0rg16 : ∀ q (hq : q < x5s7d0r.size), 16 ≤ q → q < 32 → ¬ Reach x5s7d0r[q].toFinset 7 0 0xfee8e880 := by
  have check : aliasPart x5s7d0r x5s7d0 0xfee8e880 x5maps 16 x5s7d0rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s7d0ok check
def x5s7d0rg32c : List (ℕ × ℕ) := [(0,90),(3,18),(6,18),(3,96),(6,96),(7,90)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d0rg32 : ∀ q (hq : q < x5s7d0r.size), 32 ≤ q → q < 38 → ¬ Reach x5s7d0r[q].toFinset 7 0 0xfee8e880 := by
  have check : aliasPart x5s7d0r x5s7d0 0xfee8e880 x5maps 32 x5s7d0rg32c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s7d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d0rok : correct x5s7d0r 7 0 0xfee8e880 := by
  intro q hq
  have lim : q < 38 := hq
  by_cases atMid : q < 16
  ·
    exact x5s7d0rg0 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 32
    ·
      exact x5s7d0rg16 q hq (by omega) (by omega)
    ·
      exact x5s7d0rg32 q hq (by omega) (by omega)
def x5s7d1 : Array (List Word) := #[[0x88888888,inputA,inputB,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE]]
def x5s7d1g0c : List (List ℕ × List ℕ) := [([0,12,1,16,2,20,9,3,13,4,17,5,21,6,14,7,18,8,22,10,19,11,23,15,24],[0x25,0x23,0x21,30,28,4]),([9,25,0x24,26,0x28,27,0x2c,28,0x25,29,0x29,30,0x2d,31,0x26,0x20,0x2a,0x21,0x2e,0x22,0x2b,0x23,0x2f,0x27,0x30],[0x24,0x22,0x20,31,29,13])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d1g0 : ∀ q (hq : q < x5s7d1.size), 0 ≤ q → q < 2 → ¬ Reach x5s7d1[q].toFinset 7 1 0xfee8e880 := by
  have check : part x5s7d1 0xfee8e880 7 1 x5s6d1r x5s7d0r 0 x5s7d1g0c = true := by decide +kernel
  exact part_ok x5s6d1rok x5s7d0rok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d1ok : correct x5s7d1 7 1 0xfee8e880 := by
  exact fun q hq => x5s7d1g0 q hq (Nat.zero_le _) hq
def x5s7d1r : Array (List Word) := #[[0x88888888,inputA,inputB,inputC,inputD,inputE],[0xa0a0a0a0,inputA,inputB,inputC,inputD,inputE],[0xaa00aa00,inputA,inputB,inputC,inputD,inputE],[0xaaaa0000,inputA,inputB,inputC,inputD,inputE],[inputA,0xc0c0c0c0,inputB,inputC,inputD,inputE],[inputA,0xcc00cc00,inputB,inputC,inputD,inputE],[inputA,0xcccc0000,inputB,inputC,inputD,inputE],[inputA,inputB,0xeeeeeeee,inputC,inputD,inputE],[inputA,inputB,0xf000f000,inputC,inputD,inputE],[inputA,inputB,0xf0f00000,inputC,inputD,inputE],[inputA,inputB,inputC,0xfafafafa,inputD,inputE],[inputA,inputB,inputC,0xfcfcfcfc,inputD,inputE],[inputA,inputB,inputC,0xff000000,inputD,inputE],[inputA,inputB,inputC,inputD,0xffaaffaa,inputE],[inputA,inputB,inputC,inputD,0xffccffcc,inputE],[inputA,inputB,inputC,inputD,0xfff0fff0,inputE],[inputA,inputB,inputC,inputD,inputE,0xffffaaaa],[inputA,inputB,inputC,inputD,inputE,0xffffcccc],[inputA,inputB,inputC,inputD,inputE,0xfffff0f0],[inputA,inputB,inputC,inputD,inputE,0xffffff00]]
def x5s7d1rg0c : List (ℕ × ℕ) := [(0,0),(0,6),(0,8),(0,9),(0,48),(0,50),(0,51),(1,0),(0,60),(0,61),(1,6),(1,48),(0,64),(1,8),(1,50),(1,60)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d1rg0 : ∀ q (hq : q < x5s7d1r.size), 0 ≤ q → q < 16 → ¬ Reach x5s7d1r[q].toFinset 7 1 0xfee8e880 := by
  have check : aliasPart x5s7d1r x5s7d1 0xfee8e880 x5maps 0 x5s7d1rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s7d1ok check
def x5s7d1rg16c : List (ℕ × ℕ) := [(1,9),(1,51),(1,61),(1,64)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d1rg16 : ∀ q (hq : q < x5s7d1r.size), 16 ≤ q → q < 20 → ¬ Reach x5s7d1r[q].toFinset 7 1 0xfee8e880 := by
  have check : aliasPart x5s7d1r x5s7d1 0xfee8e880 x5maps 16 x5s7d1rg16c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s7d1ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s7d1rok : correct x5s7d1r 7 1 0xfee8e880 := by
  intro q hq
  have lim : q < 20 := hq
  by_cases atMid : q < 16
  ·
    exact x5s7d1rg0 q hq (by omega) (by omega)
  ·
    exact x5s7d1rg16 q hq (by omega) (by omega)
def x5s8d0 : Array (List Word) := #[[0xffff,inputA,inputB,inputC,inputD,inputE]]
def x5s8d0g0c : List (List ℕ × List ℕ) := [([0,8,1,12,2,16,3,20,4,13,5,17,6,21,7,24,9,18,10,22,11,25,14,23,15,26,19,27],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s8d0g0 : ∀ q (hq : q < x5s8d0.size), 0 ≤ q → q < 1 → ¬ Reach x5s8d0[q].toFinset 8 0 0xfee8e880 := by
  have check : part x5s8d0 0xfee8e880 8 0 x5s7d0r #[] 0 x5s8d0g0c = true := by decide +kernel
  exact part_ok x5s7d0rok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s8d0ok : correct x5s8d0 8 0 0xfee8e880 := by
  exact fun q hq => x5s8d0g0 q hq (Nat.zero_le _) hq
def x5s8d0r : Array (List Word) := #[[0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE]]
def x5s8d0rg0c : List (ℕ × ℕ) := [(0,0),(0,1),(0,4),(0,18),(0,96)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s8d0rg0 : ∀ q (hq : q < x5s8d0r.size), 0 ≤ q → q < 5 → ¬ Reach x5s8d0r[q].toFinset 8 0 0xfee8e880 := by
  have check : aliasPart x5s8d0r x5s8d0 0xfee8e880 x5maps 0 x5s8d0rg0c = true := by decide +kernel
  exact alias_ok x5maps_ok x5s8d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s8d0rok : correct x5s8d0r 8 0 0xfee8e880 := by
  exact fun q hq => x5s8d0rg0 q hq (Nat.zero_le _) hq
def x5s8d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x5s8d1g0c : List (List ℕ × List ℕ) := [([0,7,1,10,2,13,3,16,4,11,5,14,6,17,8,15,9,18,12,19],[4,3,2,1,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s8d1g0 : ∀ q (hq : q < x5s8d1.size), 0 ≤ q → q < 1 → ¬ Reach x5s8d1[q].toFinset 8 1 0xfee8e880 := by
  have check : part x5s8d1 0xfee8e880 8 1 x5s7d1r x5s8d0r 0 x5s8d1g0c = true := by decide +kernel
  exact part_ok x5s7d1rok x5s8d0rok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x5s8d1ok : correct x5s8d1 8 1 0xfee8e880 := by
  exact fun q hq => x5s8d1g0 q hq (Nat.zero_le _) hq
def x5gates : List Gate := [⟨.and, [0,1]⟩,⟨.or, [0,1]⟩,⟨.or, [2,3]⟩,⟨.and, [2,3]⟩,⟨.or, [5,8]⟩,⟨.or, [4,9]⟩,⟨.and, [4,9]⟩,⟨.and, [7,10]⟩,⟨.and, [6,12]⟩,⟨.or, [11,13]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result5 : Verdict 0xfee8e880 := by
  apply verdict (k := 8) (by decide) (by decide) (x5s8d1ok 0 (by decide)) x5gates 14
  · simp [x5gates,mono]
  · decide
  · decide +kernel

def x6s2d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x6s2d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x6s2d1g0 : ∀ q (hq : q < x6s2d1.size), 0 ≤ q → q < 1 → ¬ Reach x6s2d1[q].toFinset 2 1 0xeaaaaaaa := by
  have check : part x6s2d1 0xeaaaaaaa 2 1 #[] #[] 0 x6s2d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x6s2d1ok : correct x6s2d1 2 1 0xeaaaaaaa := by
  exact fun q hq => x6s2d1g0 q hq (Nat.zero_le _) hq
def x6gates : List Gate := [⟨.and, [1,2]⟩,⟨.and, [3,4]⟩,⟨.and, [5,6]⟩,⟨.or, [0,7]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result6 : Verdict 0xeaaaaaaa := by
  apply verdict (k := 2) (by decide) (by decide) (x6s2d1ok 0 (by decide)) x6gates 8
  · simp [x6gates,mono]
  · decide
  · decide +kernel

def x7s3d0 : Array (List Word) := #[[inputA,inputB,inputC,0xff0fff00],[inputA,inputB,inputC,0xff33ff00],[inputA,inputB,inputC,0xffaaff00],[inputA,inputB,0xf0fff0f0,inputD],[inputA,inputB,0xf3f3f0f0,inputD],[inputA,inputB,0xfafaf0f0,inputD],[inputA,0xccffcccc,inputC,inputD],[inputA,0xcfcfcccc,inputC,inputD],[inputA,0xeeeecccc,inputC,inputD]]
def x7s3d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s3d0g0 : ∀ q (hq : q < x7s3d0.size), 0 ≤ q → q < 4 → ¬ Reach x7s3d0[q].toFinset 3 0 0xeaaaeaa8 := by
  have check : part x7s3d0 0xeaaaeaa8 3 0 #[] #[] 0 x7s3d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
def x7s3d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s3d0g4 : ∀ q (hq : q < x7s3d0.size), 4 ≤ q → q < 8 → ¬ Reach x7s3d0[q].toFinset 3 0 0xeaaaeaa8 := by
  have check : part x7s3d0 0xeaaaeaa8 3 0 #[] #[] 4 x7s3d0g4c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
def x7s3d0g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s3d0g8 : ∀ q (hq : q < x7s3d0.size), 8 ≤ q → q < 9 → ¬ Reach x7s3d0[q].toFinset 3 0 0xeaaaeaa8 := by
  have check : part x7s3d0 0xeaaaeaa8 3 0 #[] #[] 8 x7s3d0g8c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s3d0ok : correct x7s3d0 3 0 0xeaaaeaa8 := by
  intro q hq
  have lim : q < 9 := hq
  by_cases atMid : q < 4
  ·
    exact x7s3d0g0 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 8
    ·
      exact x7s3d0g4 q hq (by omega) (by omega)
    ·
      exact x7s3d0g8 q hq (by omega) (by omega)
def x7s3d1 : Array (List Word) := #[[inputA,inputB,inputC,0xffaaff00],[inputA,inputB,0xfafaf0f0,inputD],[inputA,0xeeeecccc,inputC,inputD]]
def x7s3d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[2,2,2,2]),([0,0,0,0,0,0,0,0,0,0,0,0],[5,5,5,5]),([0,0,0,0,0,0,0,0,0,0,0,0],[8,8,8,8])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s3d1g0 : ∀ q (hq : q < x7s3d1.size), 0 ≤ q → q < 3 → ¬ Reach x7s3d1[q].toFinset 3 1 0xeaaaeaa8 := by
  have check : part x7s3d1 0xeaaaeaa8 3 1 #[] x7s3d0 0 x7s3d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x7s3d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s3d1ok : correct x7s3d1 3 1 0xeaaaeaa8 := by
  exact fun q hq => x7s3d1g0 q hq (Nat.zero_le _) hq
def x7s4d0 : Array (List Word) := #[[0xff0000,inputA,inputB,inputC,inputD],[0xf0f0000,inputA,inputB,inputC,inputD],[0x33330000,inputA,inputB,inputC,inputD],[0xaaaa0000,inputA,inputB,inputC,inputD],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff5555],[inputA,inputB,inputC,inputD,0xffffcccc],[inputA,inputB,inputC,inputD,0xfffff0f0],[inputA,inputB,inputC,inputD,0xffffff00]]
def x7s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,6,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,4,0,1,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,8,0,5,0,2,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s4d0g0 : ∀ q (hq : q < x7s4d0.size), 0 ≤ q → q < 4 → ¬ Reach x7s4d0[q].toFinset 4 0 0xeaaaeaa8 := by
  have check : part x7s4d0 0xeaaaeaa8 4 0 x7s3d0 #[] 0 x7s4d0g0c = true := by decide +kernel
  exact part_ok x7s3d0ok (noRows _ _ _) check
def x7s4d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s4d0g4 : ∀ q (hq : q < x7s4d0.size), 4 ≤ q → q < 8 → ¬ Reach x7s4d0[q].toFinset 4 0 0xeaaaeaa8 := by
  have check : part x7s4d0 0xeaaaeaa8 4 0 x7s3d0 #[] 4 x7s4d0g4c = true := by decide +kernel
  exact part_ok x7s3d0ok (noRows _ _ _) check
def x7s4d0g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s4d0g8 : ∀ q (hq : q < x7s4d0.size), 8 ≤ q → q < 9 → ¬ Reach x7s4d0[q].toFinset 4 0 0xeaaaeaa8 := by
  have check : part x7s4d0 0xeaaaeaa8 4 0 x7s3d0 #[] 8 x7s4d0g8c = true := by decide +kernel
  exact part_ok x7s3d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s4d0ok : correct x7s4d0 4 0 0xeaaaeaa8 := by
  intro q hq
  have lim : q < 9 := hq
  by_cases atMid : q < 4
  ·
    exact x7s4d0g0 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 8
    ·
      exact x7s4d0g4 q hq (by omega) (by omega)
    ·
      exact x7s4d0g8 q hq (by omega) (by omega)
def x7s4d1 : Array (List Word) := #[[0xaaaa0000,inputA,inputB,inputC,inputD],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffffcccc],[inputA,inputB,inputC,inputD,0xfffff0f0],[inputA,inputB,inputC,inputD,0xffffff00]]
def x7s4d1g0c : List (List ℕ × List ℕ) := [([0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[3,3,3,3,3]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[4,4,4,4,4]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[6,6,6,6,6]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[7,7,7,7,7])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s4d1g0 : ∀ q (hq : q < x7s4d1.size), 0 ≤ q → q < 4 → ¬ Reach x7s4d1[q].toFinset 4 1 0xeaaaeaa8 := by
  have check : part x7s4d1 0xeaaaeaa8 4 1 x7s3d1 x7s4d0 0 x7s4d1g0c = true := by decide +kernel
  exact part_ok x7s3d1ok x7s4d0ok check
def x7s4d1g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[8,8,8,8,8])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s4d1g4 : ∀ q (hq : q < x7s4d1.size), 4 ≤ q → q < 5 → ¬ Reach x7s4d1[q].toFinset 4 1 0xeaaaeaa8 := by
  have check : part x7s4d1 0xeaaaeaa8 4 1 x7s3d1 x7s4d0 4 x7s4d1g4c = true := by decide +kernel
  exact part_ok x7s3d1ok x7s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s4d1ok : correct x7s4d1 4 1 0xeaaaeaa8 := by
  intro q hq
  have lim : q < 5 := hq
  by_cases atMid : q < 4
  ·
    exact x7s4d1g0 q hq (by omega) (by omega)
  ·
    exact x7s4d1g4 q hq (by omega) (by omega)
def x7s5d0 : Array (List Word) := #[[0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE]]
def x7s5d0g0c : List (List ℕ × List ℕ) := [([4,4,4,4,4,4,4,4,4,4,4,4,4,4,0x1804,4,4,4,4,4,4,0x3004,4,4,4,0x3804,4,0x4004],[]),([4,4,4,4,4,4,4,4,4,4,4,4,4,4,0x1804,4,4,4,4,4,4,0x3004,4,4,4,0x3804,4,0x4004],[]),([4,4,4,4,4,4,0x804,4,4,4,4,4,4,4,0x1804,4,4,4,4,4,4,0x3004,4,4,4,0x3804,4,0x4004],[]),([4,4,4,4,4,4,0x1004,4,4,4,4,4,4,4,0x1804,4,4,4,4,4,4,0x3004,4,4,4,0x3804,4,0x4004],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s5d0g0 : ∀ q (hq : q < x7s5d0.size), 0 ≤ q → q < 4 → ¬ Reach x7s5d0[q].toFinset 5 0 0xeaaaeaa8 := by
  have check : part x7s5d0 0xeaaaeaa8 5 0 x7s4d0 #[] 0 x7s5d0g0c = true := by decide +kernel
  exact part_ok x7s4d0ok (noRows _ _ _) check
def x7s5d0g4c : List (List ℕ × List ℕ) := [([4,4,4,4,4,4,4,0x2804,4,4,4,4,4,4,0x1804,4,4,4,4,4,4,0x3004,4,4,4,0x3804,4,0x4004],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s5d0g4 : ∀ q (hq : q < x7s5d0.size), 4 ≤ q → q < 5 → ¬ Reach x7s5d0[q].toFinset 5 0 0xeaaaeaa8 := by
  have check : part x7s5d0 0xeaaaeaa8 5 0 x7s4d0 #[] 4 x7s5d0g4c = true := by decide +kernel
  exact part_ok x7s4d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s5d0ok : correct x7s5d0 5 0 0xeaaaeaa8 := by
  intro q hq
  have lim : q < 5 := hq
  by_cases atMid : q < 4
  ·
    exact x7s5d0g0 q hq (by omega) (by omega)
  ·
    exact x7s5d0g4 q hq (by omega) (by omega)
def x7s5d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x7s5d1g0c : List (List ℕ × List ℕ) := [([1,1,1,1,1,1,1,1,1,1,1,1,1,0x1001,1,1,1,0x1801,1,0x2001],[4,3,2,1,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s5d1g0 : ∀ q (hq : q < x7s5d1.size), 0 ≤ q → q < 1 → ¬ Reach x7s5d1[q].toFinset 5 1 0xeaaaeaa8 := by
  have check : part x7s5d1 0xeaaaeaa8 5 1 x7s4d1 x7s5d0 0 x7s5d1g0c = true := by decide +kernel
  exact part_ok x7s4d1ok x7s5d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x7s5d1ok : correct x7s5d1 5 1 0xeaaaeaa8 := by
  exact fun q hq => x7s5d1g0 q hq (Nat.zero_le _) hq
def x7gates : List Gate := [⟨.and, [1,3]⟩,⟨.or, [1,3]⟩,⟨.or, [2,4]⟩,⟨.and, [2,5]⟩,⟨.or, [6,7]⟩,⟨.and, [0,9]⟩,⟨.or, [8,10]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result7 : Verdict 0xeaaaeaa8 := by
  apply verdict (k := 5) (by decide) (by decide) (x7s5d1ok 0 (by decide)) x7gates 11
  · simp [x7gates,mono]
  · decide
  · decide +kernel

def x8s3d0 : Array (List Word) := #[[inputA,inputB,inputC,0xff000000]]
def x8s3d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s3d0g0 : ∀ q (hq : q < x8s3d0.size), 0 ≤ q → q < 1 → ¬ Reach x8s3d0[q].toFinset 3 0 0xeae8e8e8 := by
  have check : part x8s3d0 0xeae8e8e8 3 0 #[] #[] 0 x8s3d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s3d0ok : correct x8s3d0 3 0 0xeae8e8e8 := by
  exact fun q hq => x8s3d0g0 q hq (Nat.zero_le _) hq
def x8s3d1 : Array (List Word) := #[[inputA,inputB,inputC,0xff000000]]
def x8s3d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s3d1g0 : ∀ q (hq : q < x8s3d1.size), 0 ≤ q → q < 1 → ¬ Reach x8s3d1[q].toFinset 3 1 0xeae8e8e8 := by
  have check : part x8s3d1 0xeae8e8e8 3 1 #[] x8s3d0 0 x8s3d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x8s3d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s3d1ok : correct x8s3d1 3 1 0xeae8e8e8 := by
  exact fun q hq => x8s3d1g0 q hq (Nat.zero_le _) hq
def x8s4d0 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x8s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s4d0g0 : ∀ q (hq : q < x8s4d0.size), 0 ≤ q → q < 1 → ¬ Reach x8s4d0[q].toFinset 4 0 0xeae8e8e8 := by
  have check : part x8s4d0 0xeae8e8e8 4 0 x8s3d0 #[] 0 x8s4d0g0c = true := by decide +kernel
  exact part_ok x8s3d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s4d0ok : correct x8s4d0 4 0 0xeae8e8e8 := by
  exact fun q hq => x8s4d0g0 q hq (Nat.zero_le _) hq
def x8s4d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x8s4d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s4d1g0 : ∀ q (hq : q < x8s4d1.size), 0 ≤ q → q < 1 → ¬ Reach x8s4d1[q].toFinset 4 1 0xeae8e8e8 := by
  have check : part x8s4d1 0xeae8e8e8 4 1 x8s3d1 x8s4d0 0 x8s4d1g0c = true := by decide +kernel
  exact part_ok x8s3d1ok x8s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x8s4d1ok : correct x8s4d1 4 1 0xeae8e8e8 := by
  exact fun q hq => x8s4d1g0 q hq (Nat.zero_le _) hq
def x8gates : List Gate := [⟨.or, [1,2]⟩,⟨.and, [1,2]⟩,⟨.and, [3,4]⟩,⟨.or, [0,6]⟩,⟨.or, [5,7]⟩,⟨.and, [8,9]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result8 : Verdict 0xeae8e8e8 := by
  apply verdict (k := 4) (by decide) (by decide) (x8s4d1ok 0 (by decide)) x8gates 10
  · simp [x8gates,mono]
  · decide
  · decide +kernel

def x9s3d0 : Array (List Word) := #[[inputA,inputB,inputC,0xff55ff00],[inputA,inputB,inputC,0xffccff00],[inputA,inputB,inputC,0xfff0ff00]]
def x9s3d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s3d0g0 : ∀ q (hq : q < x9s3d0.size), 0 ≤ q → q < 3 → ¬ Reach x9s3d0[q].toFinset 3 0 0xeae8eaa8 := by
  have check : part x9s3d0 0xeae8eaa8 3 0 #[] #[] 0 x9s3d0g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s3d0ok : correct x9s3d0 3 0 0xeae8eaa8 := by
  exact fun q hq => x9s3d0g0 q hq (Nat.zero_le _) hq
def x9s3d1 : Array (List Word) := #[[inputA,inputB,inputC,0xffccff00],[inputA,inputB,inputC,0xfff0ff00]]
def x9s3d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0],[1,1,1,1]),([0,0,0,0,0,0,0,0,0,0,0,0],[2,2,2,2])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s3d1g0 : ∀ q (hq : q < x9s3d1.size), 0 ≤ q → q < 2 → ¬ Reach x9s3d1[q].toFinset 3 1 0xeae8eaa8 := by
  have check : part x9s3d1 0xeae8eaa8 3 1 #[] x9s3d0 0 x9s3d1g0c = true := by decide +kernel
  exact part_ok (noRows _ _ _) x9s3d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s3d1ok : correct x9s3d1 3 1 0xeae8eaa8 := by
  exact fun q hq => x9s3d1g0 q hq (Nat.zero_le _) hq
def x9s4d0 : Array (List Word) := #[[0xff0000,inputA,inputB,inputC,inputD],[0x55550000,inputA,inputB,inputC,inputD],[inputA,0xcccc0000,inputB,inputC,inputD],[inputA,inputB,0xf0f00000,inputC,inputD],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffff0f0f],[inputA,inputB,inputC,inputD,0xffff3333],[inputA,inputB,inputC,inputD,0xffffaaaa],[inputA,inputB,inputC,inputD,0xffffff00]]
def x9s4d0g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s4d0g0 : ∀ q (hq : q < x9s4d0.size), 0 ≤ q → q < 4 → ¬ Reach x9s4d0[q].toFinset 4 0 0xeae8eaa8 := by
  have check : part x9s4d0 0xeae8eaa8 4 0 x9s3d0 #[] 0 x9s4d0g0c = true := by decide +kernel
  exact part_ok x9s3d0ok (noRows _ _ _) check
def x9s4d0g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s4d0g4 : ∀ q (hq : q < x9s4d0.size), 4 ≤ q → q < 8 → ¬ Reach x9s4d0[q].toFinset 4 0 0xeae8eaa8 := by
  have check : part x9s4d0 0xeae8eaa8 4 0 x9s3d0 #[] 4 x9s4d0g4c = true := by decide +kernel
  exact part_ok x9s3d0ok (noRows _ _ _) check
def x9s4d0g8c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s4d0g8 : ∀ q (hq : q < x9s4d0.size), 8 ≤ q → q < 9 → ¬ Reach x9s4d0[q].toFinset 4 0 0xeae8eaa8 := by
  have check : part x9s4d0 0xeae8eaa8 4 0 x9s3d0 #[] 8 x9s4d0g8c = true := by decide +kernel
  exact part_ok x9s3d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s4d0ok : correct x9s4d0 4 0 0xeae8eaa8 := by
  intro q hq
  have lim : q < 9 := hq
  by_cases atMid : q < 4
  ·
    exact x9s4d0g0 q hq (by omega) (by omega)
  ·
    by_cases atMid : q < 8
    ·
      exact x9s4d0g4 q hq (by omega) (by omega)
    ·
      exact x9s4d0g8 q hq (by omega) (by omega)
def x9s4d1 : Array (List Word) := #[[inputA,0xcccc0000,inputB,inputC,inputD],[inputA,inputB,0xf0f00000,inputC,inputD],[inputA,inputB,inputC,inputD,inputE],[inputA,inputB,inputC,inputD,0xffffaaaa],[inputA,inputB,inputC,inputD,0xffffff00]]
def x9s4d1g0c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[2,2,2,2,2]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],[3,3,3,3,3]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[4,4,4,4,4]),([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[7,7,7,7,7])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s4d1g0 : ∀ q (hq : q < x9s4d1.size), 0 ≤ q → q < 4 → ¬ Reach x9s4d1[q].toFinset 4 1 0xeae8eaa8 := by
  have check : part x9s4d1 0xeae8eaa8 4 1 x9s3d1 x9s4d0 0 x9s4d1g0c = true := by decide +kernel
  exact part_ok x9s3d1ok x9s4d0ok check
def x9s4d1g4c : List (List ℕ × List ℕ) := [([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[8,8,8,8,8])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s4d1g4 : ∀ q (hq : q < x9s4d1.size), 4 ≤ q → q < 5 → ¬ Reach x9s4d1[q].toFinset 4 1 0xeae8eaa8 := by
  have check : part x9s4d1 0xeae8eaa8 4 1 x9s3d1 x9s4d0 4 x9s4d1g4c = true := by decide +kernel
  exact part_ok x9s3d1ok x9s4d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s4d1ok : correct x9s4d1 4 1 0xeae8eaa8 := by
  intro q hq
  have lim : q < 5 := hq
  by_cases atMid : q < 4
  ·
    exact x9s4d1g0 q hq (by omega) (by omega)
  ·
    exact x9s4d1g4 q hq (by omega) (by omega)
def x9s5d0 : Array (List Word) := #[[0xffff,inputA,inputB,inputC,inputD,inputE],[0xff00ff,inputA,inputB,inputC,inputD,inputE],[0xf0f0f0f,inputA,inputB,inputC,inputD,inputE],[0x33333333,inputA,inputB,inputC,inputD,inputE],[0x55555555,inputA,inputB,inputC,inputD,inputE]]
def x9s5d0g0c : List (List ℕ × List ℕ) := [([4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,0x3804,4,4,4,4,0x1004,4,4,4,0x1804,4,4,0x4004],[]),([4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,0x3804,4,4,4,4,0x1004,4,4,4,0x1804,4,4,0x4004],[]),([4,4,4,4,4,4,4,0x2804,4,4,4,4,4,4,4,0x3804,4,4,4,4,0x1004,4,4,4,0x1804,4,4,0x4004],[]),([4,4,4,4,4,4,4,0x3004,4,4,4,4,4,4,4,0x3804,4,4,4,4,0x1004,4,4,4,0x1804,4,4,0x4004],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s5d0g0 : ∀ q (hq : q < x9s5d0.size), 0 ≤ q → q < 4 → ¬ Reach x9s5d0[q].toFinset 5 0 0xeae8eaa8 := by
  have check : part x9s5d0 0xeae8eaa8 5 0 x9s4d0 #[] 0 x9s5d0g0c = true := by decide +kernel
  exact part_ok x9s4d0ok (noRows _ _ _) check
def x9s5d0g4c : List (List ℕ × List ℕ) := [([4,4,4,4,4,4,0x804,4,4,4,4,4,4,4,4,0x3804,4,4,4,4,0x1004,4,4,4,0x1804,4,4,0x4004],[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s5d0g4 : ∀ q (hq : q < x9s5d0.size), 4 ≤ q → q < 5 → ¬ Reach x9s5d0[q].toFinset 5 0 0xeae8eaa8 := by
  have check : part x9s5d0 0xeae8eaa8 5 0 x9s4d0 #[] 4 x9s5d0g4c = true := by decide +kernel
  exact part_ok x9s4d0ok (noRows _ _ _) check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s5d0ok : correct x9s5d0 5 0 0xeae8eaa8 := by
  intro q hq
  have lim : q < 5 := hq
  by_cases atMid : q < 4
  ·
    exact x9s5d0g0 q hq (by omega) (by omega)
  ·
    exact x9s5d0g4 q hq (by omega) (by omega)
def x9s5d1 : Array (List Word) := #[[inputA,inputB,inputC,inputD,inputE]]
def x9s5d1g0c : List (List ℕ × List ℕ) := [([2,2,2,2,2,2,2,0x1802,2,2,2,2,2,2,2,2,0x802,2,2,0x2002],[4,3,2,1,0])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s5d1g0 : ∀ q (hq : q < x9s5d1.size), 0 ≤ q → q < 1 → ¬ Reach x9s5d1[q].toFinset 5 1 0xeae8eaa8 := by
  have check : part x9s5d1 0xeae8eaa8 5 1 x9s4d1 x9s5d0 0 x9s5d1g0c = true := by decide +kernel
  exact part_ok x9s4d1ok x9s5d0ok check
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem x9s5d1ok : correct x9s5d1 5 1 0xeae8eaa8 := by
  exact fun q hq => x9s5d1g0 q hq (Nat.zero_le _) hq
def x9gates : List Gate := [⟨.or, [1,2]⟩,⟨.or, [3,4]⟩,⟨.or, [3,5]⟩,⟨.and, [1,6]⟩,⟨.and, [2,8]⟩,⟨.or, [0,9]⟩,⟨.and, [7,10]⟩]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem result9 : Verdict 0xeae8eaa8 := by
  apply verdict (k := 5) (by decide) (by decide) (x9s5d1ok 0 (by decide)) x9gates 11
  · simp [x9gates,mono]
  · decide
  · decide +kernel

end PEqualNP.Outside.L_meta_1433_aux

open PEqualNP.Outside.L_meta_1433_aux

theorem PEqualNP.Outside.L_meta_1433 : ∀ T ∈ ({0xeaeaea80, 0xeee0e8e0, 0xeee0eac0, 0xeee8e888, 0xeee8e8a0, 0xfee8e880, 0xeaaaaaaa, 0xeaaaeaa8, 0xeae8e8e8, 0xeae8eaa8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T ht
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact result0
  · exact result1
  · exact result2
  · exact result3
  · exact result4
  · exact result5
  · exact result6
  · exact result7
  · exact result8
  · exact result9
