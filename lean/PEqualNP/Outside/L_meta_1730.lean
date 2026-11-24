import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1730_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  { gates := [
    ⟨.or, [0, 1]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [12, 0]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [7, 0]⟩,
    ⟨.or, [8, 1]⟩,
    ⟨.or, [9, 2]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.or, [11, 4]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.or, [26, 42]⟩,
    ⟨.or, [27, 43]⟩,
    ⟨.or, [28, 44]⟩,
    ⟨.or, [29, 45]⟩,
    ⟨.or, [30, 46]⟩,
    ⟨.or, [31, 47]⟩,
    ⟨.or, [32, 48]⟩,
    ⟨.or, [33, 49]⟩,
    ⟨.or, [34, 50]⟩,
    ⟨.or, [35, 51]⟩,
    ⟨.or, [36, 39]⟩,
    ⟨.or, [37, 40]⟩,
    ⟨.or, [38, 41]⟩,
    ⟨.and, [13, 52]⟩,
    ⟨.and, [25, 53]⟩,
    ⟨.and, [24, 54]⟩,
    ⟨.and, [23, 55]⟩,
    ⟨.and, [22, 56]⟩,
    ⟨.and, [21, 57]⟩,
    ⟨.and, [20, 58]⟩,
    ⟨.and, [19, 59]⟩,
    ⟨.and, [18, 60]⟩,
    ⟨.and, [17, 61]⟩,
    ⟨.and, [16, 62]⟩,
    ⟨.and, [15, 63]⟩,
    ⟨.and, [14, 64]⟩,
    ⟨.or, [65, 66]⟩,
    ⟨.or, [78, 67]⟩,
    ⟨.or, [79, 68]⟩,
    ⟨.or, [80, 69]⟩,
    ⟨.or, [81, 70]⟩,
    ⟨.or, [82, 71]⟩,
    ⟨.or, [83, 72]⟩,
    ⟨.or, [84, 73]⟩,
    ⟨.or, [85, 74]⟩,
    ⟨.or, [86, 75]⟩,
    ⟨.or, [87, 76]⟩,
    ⟨.or, [88, 77]⟩], output := 89 }

def exactBinary (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b]

lemma circuit_binary : ∀ g ∈ circuit.gates, exactBinary g := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [exactBinary]

lemma monotone : Monotone2 circuit := by
  intro g hg
  obtain ⟨ho,a,b,h⟩ := circuit_binary g hg
  exact ⟨by simpa using ho, by simp [h]⟩

lemma size : circuit.size = 64 := rfl

def word (i : ℕ) : List Nat → Nat
  | [] => 0
  | m::tail => Nat.bit (m.testBit i) (word i tail)

lemma word_read (i : ℕ) : ∀ (rows : List Nat) (j : Nat),
    (word i rows).testBit j = (rows.map fun m => m.testBit i).getD j false
  | [], j => by simp [word]
  | m :: rows, 0 => by simp [word]
  | m :: rows, j+1 => by simp [word, Nat.testBit_bit_succ, word_read i rows j]

def columns (rows : List Nat) : List Nat := List.ofFn fun i : Fin 26 => word i.val rows

def packedGate (w : List Nat) (g : Gate) : Nat :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  match g.op with
  | .and => a &&& b
  | _ => a ||| b

def computePacked (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun state g => state ++ [packedGate state g]) w

lemma packed_read (w : List Nat) (i j : ℕ) :
    (w.getD i 0).testBit j = (w.map fun a => a.testBit j).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

lemma gate_read (g : Gate) (leg : exactBinary g) (w : List Nat) (j : ℕ) :
    (packedGate w g).testBit j = g.op.eval (g.inputs.map fun i =>
      (w.map fun a => a.testBit j).getD i false) := by
  obtain ⟨ho,a,b,inputs⟩ := leg
  rcases ho with h | h
  · rw [h, inputs]
    unfold packedGate
    simp only [h, inputs, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      id_eq, List.all_nil, Bool.and_true, Nat.testBit_and]
    exact congrArg₂ (· && ·) (packed_read w a j) (packed_read w b j)
  · rw [h, inputs]
    unfold packedGate
    simp only [h, inputs, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      id_eq, List.any_nil, Bool.or_false, Nat.testBit_or]
    exact congrArg₂ (· || ·) (packed_read w a j) (packed_read w b j)

lemma computation_read (gs : List Gate) (w : List Nat) (j : ℕ)
    (leg : ∀ g ∈ gs, exactBinary g) :
    (computePacked gs w).map (fun a => a.testBit j) =
      gs.foldl (fun state g => state ++ [g.op.eval (g.inputs.map fun i => state.getD i false)])
        (w.map fun a => a.testBit j) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g tail ih =>
    change (computePacked tail (w ++ [packedGate w g])).map _ = _
    rw [ih _ (fun h hh => leg h (List.mem_cons_of_mem _ hh))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton,
      gate_read g (leg g List.mem_cons_self)]

lemma input_columns (rows : List Nat) (j : ℕ) (hj : j < rows.length) :
    ((columns rows).map fun a => a.testBit j) =
    List.ofFn (fun i : Fin 26 => (rows.getD j 0).testBit i.val) := by
  unfold columns
  rw [List.map_ofFn]
  congr 1
  funext i
  simp [word_read, List.getD_eq_getElem _ _ hj, hj]

def packedOutput (C : Circuit) (rows : List Nat) : Nat :=
  (computePacked C.gates (columns rows)).getD C.output 0

lemma output_read (C : Circuit) (shape : ∀ g ∈ C.gates, exactBinary g)
    (rows : List Nat) (j : ℕ) (hj : j < rows.length) :
    (packedOutput C rows).testBit j =
      C.eval (List.ofFn fun i : Fin 26 => (rows.getD j 0).testBit i.val) := by
  unfold packedOutput
  rw [packed_read, computation_read _ _ _ shape, input_columns rows j hj]
  rfl

def incidentList : List (Fin 13 × Fin 13) := [(0, 0), (0, 1), (0, 3), (0, 9), (1, 0), (1, 2), (1, 8), (1, 12), (2, 1), (2, 7), (2, 11), (2, 12), (3, 0), (3, 6), (3, 10), (3, 11), (4, 5), (4, 9), (4, 10), (4, 12), (5, 4), (5, 8), (5, 9), (5, 11), (6, 3), (6, 7), (6, 8), (6, 10), (7, 2), (7, 6), (7, 7), (7, 9), (8, 1), (8, 5), (8, 6), (8, 8), (9, 0), (9, 4), (9, 5), (9, 7), (10, 3), (10, 4), (10, 6), (10, 12), (11, 2), (11, 3), (11, 5), (11, 11), (12, 1), (12, 2), (12, 4), (12, 10)]

lemma incident_exact :
    ∀ p l : Fin 13, (p,l) ∈ incidentList ↔ (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) := by
  decide +kernel

def packedIncidences (rows : List Nat) : Nat :=
  incidentList.foldr (fun (p,l) acc =>
    (word p.val rows &&& word (13+l.val) rows) ||| acc) 0

lemma incident_bit {pairs : List (Fin 13 × Fin 13)} {p l : Fin 13}
    (hm : (p,l) ∈ pairs) (rows : List Nat) (j : ℕ)
    (hp : (word p.val rows).testBit j = true)
    (hl : (word (13+l.val) rows).testBit j = true) :
    (pairs.foldr (fun (pair : Fin 13 × Fin 13) acc =>
        (word pair.1.val rows &&& word (13+pair.2.val) rows) ||| acc) 0).testBit j = true := by
  induction pairs with
  | nil => simp at hm
  | cons z zs ih =>
    rcases z with ⟨u,v⟩
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
      simp [Nat.testBit_or, Nat.testBit_and, hp, hl]
    · simp only [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true]
      exact Or.inr (ih h)

def safeMask (C : Circuit) (m : Nat) : Prop :=
  (∀ p l : Fin 13, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) →
    ¬ (m.testBit p.val = true ∧ m.testBit (13+l.val) = true)) ∧
  C.eval (List.ofFn (fun j : Fin 26 => m.testBit j.val)) = false

set_option maxHeartbeats 0 in
lemma packed_safe (C : Circuit) (shape : ∀ g ∈ C.gates, exactBinary g)
    (rows : List Nat) (h : packedOutput C rows ||| packedIncidences rows = 0) :
    ∀ m ∈ rows, safeMask C m := by
  intro m hm
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hm
  have all := congrArg (fun a : Nat => a.testBit j) h
  simp only [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at all
  obtain ⟨out,bad⟩ := all
  rw [output_read C shape rows j hj,List.getD_eq_getElem _ _ hj] at out
  refine ⟨?_,out⟩
  intro p l hpair hfire
  have hcol (i : ℕ) (x : rows[j].testBit i = true) : (word i rows).testBit j = true := by
    simpa [word_read, hj, List.getD_eq_getElem _ _ hj] using x
  have impossible := incident_bit ((incident_exact p l).mpr hpair) rows j
    (hcol _ hfire.1) (hcol _ hfire.2)
  unfold packedIncidences at bad
  rw [bad] at impossible
  contradiction


def incidentMask (p l : Fin 13) : Nat := (1 <<< p.val) ||| (1 <<< (13+l.val))

def positiveMasks : List Nat := [8193, 16385, 65537, 4194305, 8194, 32770, 2097154, 33554434, 16388, 1048580, 16777220, 33554436, 8200, 524296, 8388616, 16777224, 262160, 4194320, 8388624, 33554448, 131104, 2097184, 4194336, 16777248, 65600, 1048640, 2097216, 8388672, 32896, 524416, 1048704, 4194432, 16640, 262400, 524544, 2097408, 8704, 131584, 262656, 1049088, 66560, 132096, 525312, 33555456, 34816, 67584, 264192, 16779264, 20480, 36864, 135168, 8392704]

lemma positive_membership : ∀ p l : Fin 13, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) →
    incidentMask p l ∈ positiveMasks := by decide +kernel

lemma positive_bits : ∀ (p l : Fin 13) (i : Fin 26),
    (incidentMask p l).testBit i.val = decide (i.val = p.val ∨ i.val = 13+l.val) := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma positive_result : packedOutput circuit positiveMasks = 2^positiveMasks.length-1 := by
  decide +kernel

lemma incidents : ∀ p l : Fin 13, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) →
    circuit.eval (List.ofFn (fun i : Fin 26 => decide (i.val=p.val ∨ i.val=13+l.val))) = true := by
  intro p l hi
  obtain ⟨j,hj,hEq⟩ := List.getElem_of_mem (positive_membership p l hi)
  have on : (packedOutput circuit positiveMasks).testBit j = true := by
    rw [positive_result, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hj
  rw [output_read circuit circuit_binary positiveMasks j hj, List.getD_eq_getElem _ _ hj, hEq] at on
  simpa only [positive_bits] using on

def packedBatch1 : List Nat := [8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480, 70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599, 141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204, 213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045, 304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423, 401604, 409802, 426061, 458894]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch1_ok : ∀ m ∈ packedBatch1, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch2 : List Nat := [475274, 531063, 538740, 543346, 551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770, 623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213, 696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102, 864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681, 1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch2_ok : ∀ m ∈ packedBatch2, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch3 : List Nat := [1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232, 1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803, 1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834, 1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272, 2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996, 2212376, 2230429, 2238612, 2246808]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch3_ok : ∀ m ∈ packedBatch3, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch4 : List Nat := [2254992, 2261021, 2293916, 2302100, 2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252, 2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604, 2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921, 3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256, 3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch4_ok : ∀ m ∈ packedBatch4, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch5 : List Nat := [4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718, 4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660, 4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696, 4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602, 4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374, 5111878, 5152836, 5250314, 5258496]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch5_ok : ∀ m ∈ packedBatch5, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch6 : List Nat := [5262346, 5276936, 5312778, 5376266, 5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148, 6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732, 6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716, 7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738, 8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch6_ok : ∀ m ∈ packedBatch6, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch7 : List Nat := [8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943, 8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834, 8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362, 9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547, 9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387, 9716770, 9733153, 9757728, 9963555]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch7_ok : ∀ m ∈ packedBatch7, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch8 : List Nat := [9979938, 10094595, 10223651, 10305570, 10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204, 10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173, 11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222, 12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146, 13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch8_ok : ∀ m ∈ packedBatch8, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch9 : List Nat := [14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668, 15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536, 16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944, 16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675, 17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195, 17313872, 17318482, 17334865, 17351248]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch9_ok : ∀ m ∈ packedBatch9, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch10 : List Nat := [17371666, 17383954, 17432659, 17449042, 17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857, 17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059, 18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432, 18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696, 19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch10_ok : ∀ m ∈ packedBatch10, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch11 : List Nat := [19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474, 20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850, 21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474, 22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747, 25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123, 25445506, 25559171, 25641090, 25690627]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch11_ok : ∀ m ∈ packedBatch11, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch12 : List Nat := [26215683, 26248449, 26345731, 26477571, 27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922, 29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258, 31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073, 33595744, 33604200, 33625000, 33632672, 33637032, 33653544, 33669672, 33688009, 33696192, 33704136, 33712320, 33718601, 33751432, 33820905, 33829088, 33833192]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch12_ok : ∀ m ∈ packedBatch12, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch13 : List Nat := [33841376, 33849449, 33865832, 33886376, 33894560, 33898664, 33947849, 33964232, 33980489, 34085473, 34093152, 34097760, 34105440, 34112097, 34128480, 34148896, 34211905, 34345057, 34353248, 34373729, 34398304, 34609449, 34617632, 34621480, 34636073, 34672936, 34681120, 34701608, 34736393, 34767113, 34869289, 34897961, 34934824, 34979880, 35133473, 35141664, 35393569, 35467296, 35658377, 35666048, 35670664, 35684873, 35721864, 35734152]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch13_ok : ∀ m ∈ packedBatch13, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch14 : List Nat := [35784841, 35801224, 35917961, 35983496, 36044937, 36126856, 36182529, 36706313, 36833289, 36966409, 37126153, 37230593, 37755720, 37763392, 37767752, 37782344, 37798472, 37819144, 37847816, 37882184, 37890368, 37898312, 37912904, 38015048, 38191176, 38279744, 38287424, 38292032, 38430784, 38803720, 38811904, 38867208, 38930696, 39026952, 39852552, 39864840, 39916040, 39961096, 40376832, 40900616, 41043976, 41226248, 41402376, 41433088]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch14_ok : ∀ m ∈ packedBatch14, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch15 : List Nat := [41946017, 41953696, 41962144, 41969824, 41976609, 42009504, 42017184, 42025632, 42042144, 42076545, 42084736, 42205345, 42295456, 42469921, 42486304, 42500641, 42582560, 42993953, 43002144, 43024673, 43098400, 43124993, 43517985, 43542560, 43810849, 43900960, 44042881, 44059264, 44173441, 44198016, 44567041, 45746177, 46140160, 47327488, 48777728, 49965056, 50336705, 50344384, 50348736, 50365249, 50402176, 50409856, 50463169, 50471360]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch15_ok : ∀ m ∈ packedBatch15, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def packedBatch16 : List Nat := [50495809, 50598081, 50606272, 50725057, 50749632, 50860609, 50889281, 51122241, 51281985, 51384577, 52433537, 52499072, 52695169, 52768896, 52957697, 54267905, 54530880, 54538560, 54559552, 54596352, 54698304, 55054912, 55099968, 55324736, 55500864, 55652608, 57217536, 58535936, 58721153, 58753793, 58786688, 58851713, 58925440, 59932929, 60818049, 60899968, 61210753, 61300864, 61374977, 62816257, 63013632, 64200960, 65651200, 67100672]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
lemma packedBatch16_ok : ∀ m ∈ packedBatch16, safeMask circuit m := by
  apply packed_safe circuit circuit_binary
  decide +kernel

def masks : List Nat := [packedBatch1, packedBatch2, packedBatch3, packedBatch4, packedBatch5, packedBatch6, packedBatch7, packedBatch8, packedBatch9, packedBatch10, packedBatch11, packedBatch12, packedBatch13, packedBatch14, packedBatch15, packedBatch16].flatten

set_option maxRecDepth 16000 in
lemma all_masks_safe (m : Nat) (hm : m ∈ masks) : safeMask circuit m := by
  simp only [masks, List.flatten_cons, List.flatten_nil, List.mem_append,
    List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact packedBatch1_ok _ h
  · exact packedBatch2_ok _ h
  · exact packedBatch3_ok _ h
  · exact packedBatch4_ok _ h
  · exact packedBatch5_ok _ h
  · exact packedBatch6_ok _ h
  · exact packedBatch7_ok _ h
  · exact packedBatch8_ok _ h
  · exact packedBatch9_ok _ h
  · exact packedBatch10_ok _ h
  · exact packedBatch11_ok _ h
  · exact packedBatch12_ok _ h
  · exact packedBatch13_ok _ h
  · exact packedBatch14_ok _ h
  · exact packedBatch15_ok _ h
  · exact packedBatch16_ok _ h

end PEqualNP.Outside.L_meta_1730_aux

set_option maxRecDepth 18000 in
open PEqualNP.Outside.L_meta_1730_aux in
theorem PEqualNP.Outside.L_meta_1730 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 49]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 52]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 53]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 54]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 61]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [65, 66]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [78, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [79, 68]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [80, 69]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [81, 70]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [82, 71]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [83, 72]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [84, 73]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [85, 74]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [86, 75]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [87, 76]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [88, 77]⟩], output := 89 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 64 ∧ (∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) → C.eval (List.ofFn (fun i : Fin 26 => decide (i.val = p.val ∨ i.val = 13 + l.val))) = true) ∧ (∀ m ∈ ([8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480, 70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599, 141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204, 213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045, 304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423, 401604, 409802, 426061, 458894, 475274, 531063, 538740, 543346, 551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770, 623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213, 696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102, 864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681, 1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376, 1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232, 1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803, 1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834, 1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272, 2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996, 2212376, 2230429, 2238612, 2246808, 2254992, 2261021, 2293916, 2302100, 2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252, 2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604, 2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921, 3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256, 3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728, 4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718, 4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660, 4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696, 4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602, 4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374, 5111878, 5152836, 5250314, 5258496, 5262346, 5276936, 5312778, 5376266, 5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148, 6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732, 6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716, 7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738, 8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716, 8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943, 8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834, 8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362, 9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547, 9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387, 9716770, 9733153, 9757728, 9963555, 9979938, 10094595, 10223651, 10305570, 10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204, 10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173, 11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222, 12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146, 13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282, 14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668, 15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536, 16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944, 16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675, 17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195, 17313872, 17318482, 17334865, 17351248, 17371666, 17383954, 17432659, 17449042, 17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857, 17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059, 18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432, 18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696, 19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272, 19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474, 20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850, 21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474, 22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747, 25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123, 25445506, 25559171, 25641090, 25690627, 26215683, 26248449, 26345731, 26477571, 27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922, 29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258, 31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073, 33595744, 33604200, 33625000, 33632672, 33637032, 33653544, 33669672, 33688009, 33696192, 33704136, 33712320, 33718601, 33751432, 33820905, 33829088, 33833192, 33841376, 33849449, 33865832, 33886376, 33894560, 33898664, 33947849, 33964232, 33980489, 34085473, 34093152, 34097760, 34105440, 34112097, 34128480, 34148896, 34211905, 34345057, 34353248, 34373729, 34398304, 34609449, 34617632, 34621480, 34636073, 34672936, 34681120, 34701608, 34736393, 34767113, 34869289, 34897961, 34934824, 34979880, 35133473, 35141664, 35393569, 35467296, 35658377, 35666048, 35670664, 35684873, 35721864, 35734152, 35784841, 35801224, 35917961, 35983496, 36044937, 36126856, 36182529, 36706313, 36833289, 36966409, 37126153, 37230593, 37755720, 37763392, 37767752, 37782344, 37798472, 37819144, 37847816, 37882184, 37890368, 37898312, 37912904, 38015048, 38191176, 38279744, 38287424, 38292032, 38430784, 38803720, 38811904, 38867208, 38930696, 39026952, 39852552, 39864840, 39916040, 39961096, 40376832, 40900616, 41043976, 41226248, 41402376, 41433088, 41946017, 41953696, 41962144, 41969824, 41976609, 42009504, 42017184, 42025632, 42042144, 42076545, 42084736, 42205345, 42295456, 42469921, 42486304, 42500641, 42582560, 42993953, 43002144, 43024673, 43098400, 43124993, 43517985, 43542560, 43810849, 43900960, 44042881, 44059264, 44173441, 44198016, 44567041, 45746177, 46140160, 47327488, 48777728, 49965056, 50336705, 50344384, 50348736, 50365249, 50402176, 50409856, 50463169, 50471360, 50495809, 50598081, 50606272, 50725057, 50749632, 50860609, 50889281, 51122241, 51281985, 51384577, 52433537, 52499072, 52695169, 52768896, 52957697, 54267905, 54530880, 54538560, 54559552, 54596352, 54698304, 55054912, 55099968, 55324736, 55500864, 55652608, 57217536, 58535936, 58721153, 58753793, 58786688, 58851713, 58925440, 59932929, 60818049, 60899968, 61210753, 61300864, 61374977, 62816257, 63013632, 64200960, 65651200, 67100672] : List ℕ), (∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) → ¬ (Nat.testBit m p.val = true ∧ Nat.testBit m (13 + l.val) = true)) ∧ C.eval (List.ofFn (fun j : Fin 26 => Nat.testBit m j.val)) = false) := by
  intro C hC
  have eq : C = circuit := hC
  subst C
  exact ⟨monotone, size, incidents, all_masks_safe⟩
