import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4027_719
    (classify : ∀ (C : Circuit),
    let E := fun p l : Fin 13 => l ∈ ([0,5,11,2,6,12] : List (Fin 13)) ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)
    let Z := fun (y : Fin 13 → Bool) (l : Fin 13) => decide (∀ p, E p l → y p=false)
    let F := fun (x : Fin 26 → Bool) => C.eval (List.ofFn x)
    (∀ g ∈ C.gates, g.op=GateOp.and ∨ g.op=GateOp.or) →
    (∀ p l, E p l → F (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))=true) →
    (∀ y, (∀ p, y p=false → ∃ l, E p l ∧ Z y l=true) → F (fun i : Fin 26 => if i.val < 13 then y (Fin.ofNat 13 i.val) else Z y (Fin.ofNat 13 (i.val-13)))=false) →
    ∀ x, F x=true ↔ ∃ p l, E p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true)
    (synth : let seed : Circuit := ⟨([129, 387, 795, 320, 477, 451, 543, 584, 737, 581, 803, 384, 741] : List Nat).map (fun u => ⟨.or, [u % 64,u/64]⟩), 0⟩
let E := fun p l : Fin 13 => l ∈ ([0,5,11,2,6,12] : List (Fin 13)) ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)
let Z := fun (y : Fin 13 → Bool) (l : Fin 13) => decide (∀ p, E p l → y p=false)
∃ D : Circuit, D.size ≤ 28 ∧ D.output < 39 + D.size ∧
  (∀ j g, D.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = .or) ∧
    ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a < 39+j ∧ b < 39+j) ∧
  let F := fun (x : Fin 26 → Bool) => D.eval (seed.wires (List.ofFn x))
  (∀ p l, E p l → F (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))=true) ∧
  ∀ y, (∀ p, y p=false → ∃ l, E p l ∧ Z y l=true) → F (fun i : Fin 26 => if i.val < 13 then y (Fin.ofNat 13 i.val) else Z y (Fin.ofNat 13 (i.val-13)))=false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (59 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size ∧ (26 : ℕ) ≤ x2 ∧ x2 < (26 : ℕ) + x1.size ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ (∀ (x3 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ)))) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x5 ≠ (1 : Fin (13 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true := by
  have wire : ∀ (C : Circuit) (w : List Bool) (j : ℕ) (g : Gate) (a b : ℕ),
    C.gates[j]? = some g → g.inputs = [a,b] → a < w.length+j → b < w.length+j →
    (C.wires w).getD (w.length+j) false =
      g.op.eval [(C.wires w).getD a false,(C.wires w).getD b false] := by
    have keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        ((Circuit.mk gs 0).wires w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change ((Circuit.mk gs 0).wires (w ++ [_])).getD i false = _
        rw [ih _ (by simp; omega)]
        exact List.getD_append _ _ _ _ hi
    rintro ⟨gs,o⟩ w j g a b h hin ha hb
    induction gs generalizing w j with
    | nil => simp at h
    | cons t ts ih =>
      cases j with
      | zero =>
        have eq : t = g := Option.some.inj h
        subst t
        simp only [Nat.add_zero] at ha hb ⊢
        let v := g.op.eval (g.inputs.map fun i => w.getD i false)
        change ((Circuit.mk ts 0).wires (w++[v])).getD w.length false = g.op.eval [((Circuit.mk ts 0).wires (w++[v])).getD a false,((Circuit.mk ts 0).wires (w++[v])).getD b false]
        rw [keeps _ _ _ (by simp),keeps _ _ _ (by simp; omega),keeps _ _ _ (by simp; omega),List.getD_append _ _ _ _ ha,List.getD_append _ _ _ _ hb]
        simp [v,hin]
      | succ k =>
        let v := t.op.eval (t.inputs.map fun i => w.getD i false)
        change ((Circuit.mk ts o).wires (w++[v])).getD (w.length+(k+1)) false = g.op.eval [((Circuit.mk ts o).wires (w++[v])).getD a false,((Circuit.mk ts o).wires (w++[v])).getD b false]
        have e := ih (w++[v]) k h (by simp; omega) (by simp; omega)
        simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm 1 k] using e
  let P : List Gate := ([129, 387, 795, 320, 477, 451, 543, 584, 737, 581, 803, 384, 741] : List ℕ).map (fun n => (⟨GateOp.or, [n % 64,n / 64]⟩ : Gate))
  let S := Circuit.mk P 0
  obtain ⟨D,hs,ho,hd,hpos,hneg⟩ := synth
  have hgrid : ∀ x : Fin 26 → Bool, D.eval (S.wires (List.ofFn x)) = true ↔
      ∃ p l : Fin 13, l ∈ ([0,5,11,2,6,12] : List (Fin 13)) ∧
        (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
    let D' : Circuit := ⟨P ++ D.gates, D.output⟩
    have heval (x : Fin 26 → Bool) : D'.eval (List.ofFn x) = D.eval (S.wires (List.ofFn x)) := by
      delta Circuit.eval
      delta Circuit.wires
      simp only [D', S, List.foldl_append]
    have hmono : ∀ g ∈ D'.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      change g ∈ P ++ D.gates at hg
      rcases List.mem_append.mp hg with hp|hh
      · change g ∈ List.map _ _ at hp
        rcases List.mem_map.mp hp with ⟨i,hi,rfl⟩
        exact Or.inr rfl
      · obtain ⟨i,hi,hg'⟩ := List.getElem_of_mem hh
        exact (hd i g (by simp [hi,hg'])).1
    have hcl := classify D' hmono (by
      intro p l he
      exact (heval _).trans (hpos p l he)) (by
      intro y hy
      exact (heval _).trans (hneg y hy))
    intro x
    rw [← heval]
    simpa only [and_assoc] using hcl x
  let r := 39+D.size
  have hr : r=39+D.size := rfl
  let tail : List Gate := [(⟨.or,[28,4]⟩ : Gate),
    (⟨.and,[r+0,16]⟩ : Gate),
    (⟨.or,[30,4]⟩ : Gate),
    (⟨.and,[r+2,17]⟩ : Gate),
    (⟨.or,[32,10]⟩ : Gate),
    (⟨.and,[r+4,20]⟩ : Gate),
    (⟨.or,[34,4]⟩ : Gate),
    (⟨.and,[r+6,21]⟩ : Gate),
    (⟨.or,[36,10]⟩ : Gate),
    (⟨.and,[r+8,22]⟩ : Gate),
    (⟨.or,[38,10]⟩ : Gate),
    (⟨.and,[r+10,23]⟩ : Gate),
    (⟨.or,[r+1,r+3]⟩ : Gate),
    (⟨.or,[r+12,r+5]⟩ : Gate),
    (⟨.or,[r+13,r+7]⟩ : Gate),
    (⟨.or,[r+14,r+9]⟩ : Gate),
    (⟨.or,[r+15,r+11]⟩ : Gate),
    (⟨.or,[r+16,D.output]⟩ : Gate)]
  let C : Circuit := ⟨(P++D.gates)++tail,r+17⟩
  have plen : P.length = 13 := rfl
  have tlen : tail.length = 18 := rfl
  have sz : C.size = 31+D.size := by
    change ((P++D.gates)++tail).length = _
    delta Circuit.size
    simp only [List.length_append,plen,tlen]
    omega
  have hplen : (P++D.gates).length = 13+D.size := by
    delta Circuit.size
    rw [List.length_append,plen]
  have pget (k : ℕ) (hk : k<13) : C.gates[k]? = P[k]? := by
    change ((P++D.gates)++tail)[k]? = _
    rw [List.getElem?_append_left (by rw [hplen]; omega), List.getElem?_append_left (by omega)]
  have tget (k : ℕ) : C.gates[13+D.size+k]? = tail[k]? := by
    change ((P++D.gates)++tail)[13+D.size+k]? = _
    rw [List.getElem?_append_right (by rw [hplen]; omega),hplen]
    simp
  let legal (x : ℕ) (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b, g.inputs = [a,b] ∧ a≠b ∧ a<x ∧ b<x
  have shape (i : ℕ) (g : Gate) (h : C.gates[i]? = some g) : legal (26+i) g := by
    by_cases hp : i<13
    · rw [pget i hp] at h
      interval_cases i <;> change some _ = some g at h <;> cases h <;>
        exact ⟨Or.inr rfl,_,_,rfl,by decide,by decide,by decide⟩
    by_cases hmid : i<13+D.size
    · have hh : D.gates[i-13]? = some g := by
        change ((P++D.gates)++tail)[i]? = _ at h
        rw [List.getElem?_append_left (by omega),List.getElem?_append_right (by omega),plen] at h
        exact h
      obtain ⟨op,a,b,hx,hab,ha,hb⟩ := hd _ _ hh
      exact ⟨op,a,b,hx,hab,by omega,by omega⟩
    let k := i-(13+D.size)
    have ik : i=13+D.size+k := by dsimp [k]; omega
    rw [ik,tget] at h
    have hk : k<18 := by
      obtain ⟨hb,_⟩ := List.getElem?_eq_some_iff.mp h
      omega
    rw [ik]
    clear ik
    interval_cases k <;> change some _ = some g at h <;> cases h <;>
      first | exact ⟨Or.inl rfl,_,_,rfl,by omega,by omega,by omega⟩
            | exact ⟨Or.inr rfl,_,_,rfl,by omega,by omega,by omega⟩
  have keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      ((Circuit.mk gs 0).wires w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (w ++ [_])).getD i false = _
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi
  have lengthW (gs : List Gate) (w : List Bool) : ((Circuit.mk gs 0).wires w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs 0).wires (w++[_])).length = _
      rw [ih]
      simp
      omega
  have raw (x : Fin 26 → Bool) (i : Fin 26) :
      (C.wires (List.ofFn x)).getD i.val false = x i := by
    change ((Circuit.mk C.gates 0).wires _).getD i.val false = _
    rw [keeps _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have rin (x : Fin 26 → Bool) (n : ℕ) (hn : n<26) : (C.wires (List.ofFn x)).getD n false = x ⟨n,hn⟩ := raw x ⟨n,hn⟩
  have middle (x : Fin 26 → Bool) :
      (C.wires (List.ofFn x)).getD D.output false = D.eval (S.wires (List.ofFn x)) := by
    have w (v : List Bool) : C.wires v = (Circuit.mk tail 0).wires (D.wires (S.wires v)) := by
      delta Circuit.wires
      simp only [C,List.foldl_append,S]
    rw [w,keeps]
    · rfl
    · change D.output < ((Circuit.mk D.gates 0).wires ((Circuit.mk P 0).wires (List.ofFn x))).length
      rw [lengthW,lengthW,plen,List.length_ofFn]
      exact ho
  have step (x : Fin 26 → Bool) (j a b : ℕ) (op : GateOp)
      (hj : C.gates[j]? = some ⟨op,[a,b]⟩) (ha : a<26+j) (hb : b<26+j) :
      (C.wires (List.ofFn x)).getD (26+j) false =
        op.eval [(C.wires (List.ofFn x)).getD a false,(C.wires (List.ofFn x)).getD b false] := by
    simpa only [List.length_ofFn] using wire C (List.ofFn x) j ⟨op,[a,b]⟩ a b hj rfl (by simpa only [List.length_ofFn]) (by simpa only [List.length_ofFn])
  have or2 (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  have and2 (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
  have go (x : Fin 26 → Bool) :
      (C.wires (List.ofFn x)).getD 26 false = (x 1 || x 2) := by
    change (C.wires (List.ofFn x)).getD (26+0) false = _
    rw [step x 0 1 2 .or (by rw [pget 0 (by decide)]; rfl) (by decide) (by decide),or2,rin x 1 (by decide),rin x 2 (by decide)]
    rfl
  refine ⟨C,26,by omega,show 26 ≤ r+17 by omega,show r+17 < 26+C.size by omega,
    by decide,by omega,shape,go,?_⟩
  intro x
  let v := fun i : ℕ => (C.wires (List.ofFn x)).getD i false
  have inn (i : ℕ) (hi : i<26) : v i = x ⟨i,hi⟩ := rin x i hi
  have mid : v D.output = D.eval (S.wires (List.ofFn x)) := middle x
  have p1 : v 27 = (v 3 || v 6) := by
    have h := step x 1 3 6 .or (by rw [pget 1 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p2 : v 28 = (v 27 || v 12) := by
    have h := step x 2 27 12 .or (by rw [pget 2 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p3 : v 29 = (v 0 || v 5) := by
    have h := step x 3 0 5 .or (by rw [pget 3 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p4 : v 30 = (v 29 || v 7) := by
    have h := step x 4 29 7 .or (by rw [pget 4 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p5 : v 31 = (v 3 || v 7) := by
    have h := step x 5 3 7 .or (by rw [pget 5 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p6 : v 32 = (v 31 || v 8) := by
    have h := step x 6 31 8 .or (by rw [pget 6 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p7 : v 33 = (v 8 || v 9) := by
    have h := step x 7 8 9 .or (by rw [pget 7 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p8 : v 34 = (v 33 || v 11) := by
    have h := step x 8 33 11 .or (by rw [pget 8 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p9 : v 35 = (v 5 || v 9) := by
    have h := step x 9 5 9 .or (by rw [pget 9 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p10 : v 36 = (v 35 || v 12) := by
    have h := step x 10 35 12 .or (by rw [pget 10 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p11 : v 37 = (v 0 || v 6) := by
    have h := step x 11 0 6 .or (by rw [pget 11 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have p12 : v 38 = (v 37 || v 11) := by
    have h := step x 12 37 11 .or (by rw [pget 12 (by decide)]; rfl) (by omega) (by omega)
    rw [or2] at h
    exact h
  have t0 : v (r+0) = (v 28 || v 4) := by
    have h := step x (13+D.size+0) 28 4 .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+0=26+(13+D.size+0) by omega]; exact h
  have t1 : v (r+1) = (v (r+0) && v 16) := by
    have h := step x (13+D.size+1) (r+0) 16 .and (by rw [tget]; rfl) (by omega) (by omega)
    rw [and2] at h
    rw [show r+1=26+(13+D.size+1) by omega]; exact h
  have t2 : v (r+2) = (v 30 || v 4) := by
    have h := step x (13+D.size+2) 30 4 .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+2=26+(13+D.size+2) by omega]; exact h
  have t3 : v (r+3) = (v (r+2) && v 17) := by
    have h := step x (13+D.size+3) (r+2) 17 .and (by rw [tget]; rfl) (by omega) (by omega)
    rw [and2] at h
    rw [show r+3=26+(13+D.size+3) by omega]; exact h
  have t4 : v (r+4) = (v 32 || v 10) := by
    have h := step x (13+D.size+4) 32 10 .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+4=26+(13+D.size+4) by omega]; exact h
  have t5 : v (r+5) = (v (r+4) && v 20) := by
    have h := step x (13+D.size+5) (r+4) 20 .and (by rw [tget]; rfl) (by omega) (by omega)
    rw [and2] at h
    rw [show r+5=26+(13+D.size+5) by omega]; exact h
  have t6 : v (r+6) = (v 34 || v 4) := by
    have h := step x (13+D.size+6) 34 4 .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+6=26+(13+D.size+6) by omega]; exact h
  have t7 : v (r+7) = (v (r+6) && v 21) := by
    have h := step x (13+D.size+7) (r+6) 21 .and (by rw [tget]; rfl) (by omega) (by omega)
    rw [and2] at h
    rw [show r+7=26+(13+D.size+7) by omega]; exact h
  have t8 : v (r+8) = (v 36 || v 10) := by
    have h := step x (13+D.size+8) 36 10 .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+8=26+(13+D.size+8) by omega]; exact h
  have t9 : v (r+9) = (v (r+8) && v 22) := by
    have h := step x (13+D.size+9) (r+8) 22 .and (by rw [tget]; rfl) (by omega) (by omega)
    rw [and2] at h
    rw [show r+9=26+(13+D.size+9) by omega]; exact h
  have t10 : v (r+10) = (v 38 || v 10) := by
    have h := step x (13+D.size+10) 38 10 .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+10=26+(13+D.size+10) by omega]; exact h
  have t11 : v (r+11) = (v (r+10) && v 23) := by
    have h := step x (13+D.size+11) (r+10) 23 .and (by rw [tget]; rfl) (by omega) (by omega)
    rw [and2] at h
    rw [show r+11=26+(13+D.size+11) by omega]; exact h
  have t12 : v (r+12) = (v (r+1) || v (r+3)) := by
    have h := step x (13+D.size+12) (r+1) (r+3) .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+12=26+(13+D.size+12) by omega]; exact h
  have t13 : v (r+13) = (v (r+12) || v (r+5)) := by
    have h := step x (13+D.size+13) (r+12) (r+5) .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+13=26+(13+D.size+13) by omega]; exact h
  have t14 : v (r+14) = (v (r+13) || v (r+7)) := by
    have h := step x (13+D.size+14) (r+13) (r+7) .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+14=26+(13+D.size+14) by omega]; exact h
  have t15 : v (r+15) = (v (r+14) || v (r+9)) := by
    have h := step x (13+D.size+15) (r+14) (r+9) .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+15=26+(13+D.size+15) by omega]; exact h
  have t16 : v (r+16) = (v (r+15) || v (r+11)) := by
    have h := step x (13+D.size+16) (r+15) (r+11) .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+16=26+(13+D.size+16) by omega]; exact h
  have t17 : v (r+17) = (v (r+16) || v D.output) := by
    have h := step x (13+D.size+17) (r+16) D.output .or (by rw [tget]; rfl) (by omega) (by omega)
    rw [or2] at h
    rw [show r+17=26+(13+D.size+17) by omega]; exact h
  change v (r+17) = true ↔ _
  rw [t17,t16,t15,t14,t13,t12,t11,t10,t9,t8,t7,t6,t5,t4,t3,t2,t1,t0,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,mid]
  simp only [inn 0 (by decide),inn 3 (by decide),inn 4 (by decide),inn 5 (by decide),inn 6 (by decide),inn 7 (by decide),inn 8 (by decide),inn 9 (by decide),inn 10 (by decide),inn 11 (by decide),inn 12 (by decide),inn 16 (by decide),inn 17 (by decide),inn 20 (by decide),inn 21 (by decide),inn 22 (by decide),inn 23 (by decide),Bool.or_eq_true,Bool.and_eq_true,hgrid]
  let G := fun p l : Fin 13 => l ∈ ([0,5,11,2,6,12] : List (Fin 13)) ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)
  let A := fun p l : Fin 13 => (p=3 ∨ p=6 ∨ p=12 ∨ p=4) ∧ l=3 ∨ (p=0 ∨ p=5 ∨ p=7 ∨ p=4) ∧ l=4 ∨ (p=3 ∨ p=7 ∨ p=8 ∨ p=10) ∧ l=7 ∨ (p=8 ∨ p=9 ∨ p=11 ∨ p=4) ∧ l=8 ∨ (p=5 ∨ p=9 ∨ p=12 ∨ p=10) ∧ l=9 ∨ (p=0 ∨ p=6 ∨ p=11 ∨ p=10) ∧ l=10
  have part : ∀ p l : Fin 13, (l≠1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)) ↔ A p l ∨ G p l := by
    dsimp only [A,G]
    decide +kernel
  have fixed : (∃ p l : Fin 13, A p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ↔
      ((x 3 = true ∨ x 6 = true ∨ x 12 = true ∨ x 4 = true) ∧ x 16 = true ∨ (x 0 = true ∨ x 5 = true ∨ x 7 = true ∨ x 4 = true) ∧ x 17 = true ∨ (x 3 = true ∨ x 7 = true ∨ x 8 = true ∨ x 10 = true) ∧ x 20 = true ∨ (x 8 = true ∨ x 9 = true ∨ x 11 = true ∨ x 4 = true) ∧ x 21 = true ∨ (x 5 = true ∨ x 9 = true ∨ x 12 = true ∨ x 10 = true) ∧ x 22 = true ∨ (x 0 = true ∨ x 6 = true ∨ x 11 = true ∨ x 10 = true) ∧ x 23 = true) := by
    constructor
    · rintro ⟨p,l,hp,hx,hy⟩
      dsimp only [A] at hp
      rcases hp with ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩
      · rcases h with rfl|rfl|rfl|rfl
        · exact (Or.inl ⟨(Or.inl hx),hy⟩)
        · exact (Or.inl ⟨(Or.inr (Or.inl hx)),hy⟩)
        · exact (Or.inl ⟨(Or.inr (Or.inr (Or.inl hx))),hy⟩)
        · exact (Or.inl ⟨(Or.inr (Or.inr (Or.inr hx))),hy⟩)
      · rcases h with rfl|rfl|rfl|rfl
        · exact (Or.inr (Or.inl ⟨(Or.inl hx),hy⟩))
        · exact (Or.inr (Or.inl ⟨(Or.inr (Or.inl hx)),hy⟩))
        · exact (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inl hx))),hy⟩))
        · exact (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inr hx))),hy⟩))
      · rcases h with rfl|rfl|rfl|rfl
        · exact (Or.inr (Or.inr (Or.inl ⟨(Or.inl hx),hy⟩)))
        · exact (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inl hx)),hy⟩)))
        · exact (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inl hx))),hy⟩)))
        · exact (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inr hx))),hy⟩)))
      · rcases h with rfl|rfl|rfl|rfl
        · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inl hx),hy⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inl hx)),hy⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inl hx))),hy⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inr hx))),hy⟩))))
      · rcases h with rfl|rfl|rfl|rfl
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inl hx),hy⟩)))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inl hx)),hy⟩)))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inl hx))),hy⟩)))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(Or.inr (Or.inr (Or.inr hx))),hy⟩)))))
      · rcases h with rfl|rfl|rfl|rfl
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(Or.inl hx),hy⟩)))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(Or.inr (Or.inl hx)),hy⟩)))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(Or.inr (Or.inr (Or.inl hx))),hy⟩)))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(Or.inr (Or.inr (Or.inr hx))),hy⟩)))))
    · intro h
      rcases h with ⟨h,hx⟩ | ⟨h,hx⟩ | ⟨h,hx⟩ | ⟨h,hx⟩ | ⟨h,hx⟩ | ⟨h,hx⟩
      · rcases h with h|h|h|h
        · exact ⟨3,3,by decide,h,hx⟩
        · exact ⟨6,3,by decide,h,hx⟩
        · exact ⟨12,3,by decide,h,hx⟩
        · exact ⟨4,3,by decide,h,hx⟩
      · rcases h with h|h|h|h
        · exact ⟨0,4,by decide,h,hx⟩
        · exact ⟨5,4,by decide,h,hx⟩
        · exact ⟨7,4,by decide,h,hx⟩
        · exact ⟨4,4,by decide,h,hx⟩
      · rcases h with h|h|h|h
        · exact ⟨3,7,by decide,h,hx⟩
        · exact ⟨7,7,by decide,h,hx⟩
        · exact ⟨8,7,by decide,h,hx⟩
        · exact ⟨10,7,by decide,h,hx⟩
      · rcases h with h|h|h|h
        · exact ⟨8,8,by decide,h,hx⟩
        · exact ⟨9,8,by decide,h,hx⟩
        · exact ⟨11,8,by decide,h,hx⟩
        · exact ⟨4,8,by decide,h,hx⟩
      · rcases h with h|h|h|h
        · exact ⟨5,9,by decide,h,hx⟩
        · exact ⟨9,9,by decide,h,hx⟩
        · exact ⟨12,9,by decide,h,hx⟩
        · exact ⟨10,9,by decide,h,hx⟩
      · rcases h with h|h|h|h
        · exact ⟨0,10,by decide,h,hx⟩
        · exact ⟨6,10,by decide,h,hx⟩
        · exact ⟨11,10,by decide,h,hx⟩
        · exact ⟨10,10,by decide,h,hx⟩
  have unite : (∃ p l : Fin 13, l≠1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) ↔
      (∃ p l : Fin 13, A p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) ∨
      (∃ p l : Fin 13, G p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) := by
    constructor
    · rintro ⟨p,l,hn,hr,hx,hy⟩
      rcases (part p l).mp ⟨hn,hr⟩ with h|h
      · exact Or.inl ⟨p,l,h,hx,hy⟩
      · exact Or.inr ⟨p,l,h,hx,hy⟩
    · rintro (⟨p,l,h,hx,hy⟩ | ⟨p,l,h,hx,hy⟩)
      · exact ⟨p,l,((part p l).mpr (Or.inl h)).1,((part p l).mpr (Or.inl h)).2,hx,hy⟩
      · exact ⟨p,l,((part p l).mpr (Or.inr h)).1,((part p l).mpr (Or.inr h)).2,hx,hy⟩
  rw [unite, fixed]
  dsimp only [G]
  simp only [and_assoc,or_assoc]
  rfl
