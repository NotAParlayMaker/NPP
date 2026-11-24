import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1730

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 49]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 52]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 53]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 54]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 61]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [65, 66]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [78, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [79, 68]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [80, 69]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [81, 70]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [82, 71]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [83, 72]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [84, 73]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [85, 74]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [86, 75]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [87, 76]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [88, 77]⟩], output := 89 }

set_option maxRecDepth 4000 in
def nonIncList : List ℕ := [8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480, 70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599, 141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204, 213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045, 304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423, 401604, 409802, 426061, 458894, 475274, 531063, 538740, 543346, 551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770, 623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213, 696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102, 864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681, 1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376, 1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232, 1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803, 1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834, 1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272, 2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996, 2212376, 2230429, 2238612, 2246808, 2254992, 2261021, 2293916, 2302100, 2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252, 2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604, 2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921, 3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256, 3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728, 4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718, 4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660, 4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696, 4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602, 4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374, 5111878, 5152836, 5250314, 5258496, 5262346, 5276936, 5312778, 5376266, 5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148, 6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732, 6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716, 7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738, 8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716, 8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943, 8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834, 8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362, 9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547, 9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387, 9716770, 9733153, 9757728, 9963555, 9979938, 10094595, 10223651, 10305570, 10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204, 10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173, 11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222, 12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146, 13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282, 14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668, 15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536, 16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944, 16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675, 17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195, 17313872, 17318482, 17334865, 17351248, 17371666, 17383954, 17432659, 17449042, 17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857, 17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059, 18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432, 18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696, 19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272, 19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474, 20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850, 21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474, 22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747, 25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123, 25445506, 25559171, 25641090, 25690627, 26215683, 26248449, 26345731, 26477571, 27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922, 29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258, 31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073, 33595744, 33604200, 33625000, 33632672, 33637032, 33653544, 33669672, 33688009, 33696192, 33704136, 33712320, 33718601, 33751432, 33820905, 33829088, 33833192, 33841376, 33849449, 33865832, 33886376, 33894560, 33898664, 33947849, 33964232, 33980489, 34085473, 34093152, 34097760, 34105440, 34112097, 34128480, 34148896, 34211905, 34345057, 34353248, 34373729, 34398304, 34609449, 34617632, 34621480, 34636073, 34672936, 34681120, 34701608, 34736393, 34767113, 34869289, 34897961, 34934824, 34979880, 35133473, 35141664, 35393569, 35467296, 35658377, 35666048, 35670664, 35684873, 35721864, 35734152, 35784841, 35801224, 35917961, 35983496, 36044937, 36126856, 36182529, 36706313, 36833289, 36966409, 37126153, 37230593, 37755720, 37763392, 37767752, 37782344, 37798472, 37819144, 37847816, 37882184, 37890368, 37898312, 37912904, 38015048, 38191176, 38279744, 38287424, 38292032, 38430784, 38803720, 38811904, 38867208, 38930696, 39026952, 39852552, 39864840, 39916040, 39961096, 40376832, 40900616, 41043976, 41226248, 41402376, 41433088, 41946017, 41953696, 41962144, 41969824, 41976609, 42009504, 42017184, 42025632, 42042144, 42076545, 42084736, 42205345, 42295456, 42469921, 42486304, 42500641, 42582560, 42993953, 43002144, 43024673, 43098400, 43124993, 43517985, 43542560, 43810849, 43900960, 44042881, 44059264, 44173441, 44198016, 44567041, 45746177, 46140160, 47327488, 48777728, 49965056, 50336705, 50344384, 50348736, 50365249, 50402176, 50409856, 50463169, 50471360, 50495809, 50598081, 50606272, 50725057, 50749632, 50860609, 50889281, 51122241, 51281985, 51384577, 52433537, 52499072, 52695169, 52768896, 52957697, 54267905, 54530880, 54538560, 54559552, 54596352, 54698304, 55054912, 55099968, 55324736, 55500864, 55652608, 57217536, 58535936, 58721153, 58753793, 58786688, 58851713, 58925440, 59932929, 60818049, 60899968, 61210753, 61300864, 61374977, 62816257, 63013632, 64200960, 65651200, 67100672]

def chunk0 : List ℕ := [8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480, 70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599, 141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204, 213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045, 304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423, 401604, 409802, 426061, 458894, 475274, 531063, 538740, 543346, 551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770, 623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213, 696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102, 864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681, 1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376]
def chunk1 : List ℕ := [1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232, 1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803, 1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834, 1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272, 2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996, 2212376, 2230429, 2238612, 2246808, 2254992, 2261021, 2293916, 2302100, 2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252, 2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604, 2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921, 3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256, 3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728]
def chunk2 : List ℕ := [4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718, 4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660, 4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696, 4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602, 4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374, 5111878, 5152836, 5250314, 5258496, 5262346, 5276936, 5312778, 5376266, 5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148, 6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732, 6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716, 7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738, 8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716]
def chunk3 : List ℕ := [8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943, 8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834, 8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362, 9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547, 9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387, 9716770, 9733153, 9757728, 9963555, 9979938, 10094595, 10223651, 10305570, 10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204, 10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173, 11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222, 12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146, 13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282]
def chunk4 : List ℕ := [14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668, 15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536, 16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944, 16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675, 17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195, 17313872, 17318482, 17334865, 17351248, 17371666, 17383954, 17432659, 17449042, 17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857, 17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059, 18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432, 18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696, 19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272]
def chunk5 : List ℕ := [19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474, 20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850, 21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474, 22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747, 25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123, 25445506, 25559171, 25641090, 25690627, 26215683, 26248449, 26345731, 26477571, 27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922, 29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258, 31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073, 33595744, 33604200, 33625000, 33632672, 33637032, 33653544, 33669672, 33688009, 33696192, 33704136, 33712320, 33718601, 33751432, 33820905, 33829088, 33833192]
def chunk6 : List ℕ := [33841376, 33849449, 33865832, 33886376, 33894560, 33898664, 33947849, 33964232, 33980489, 34085473, 34093152, 34097760, 34105440, 34112097, 34128480, 34148896, 34211905, 34345057, 34353248, 34373729, 34398304, 34609449, 34617632, 34621480, 34636073, 34672936, 34681120, 34701608, 34736393, 34767113, 34869289, 34897961, 34934824, 34979880, 35133473, 35141664, 35393569, 35467296, 35658377, 35666048, 35670664, 35684873, 35721864, 35734152, 35784841, 35801224, 35917961, 35983496, 36044937, 36126856, 36182529, 36706313, 36833289, 36966409, 37126153, 37230593, 37755720, 37763392, 37767752, 37782344, 37798472, 37819144, 37847816, 37882184, 37890368, 37898312, 37912904, 38015048, 38191176, 38279744, 38287424, 38292032, 38430784, 38803720, 38811904, 38867208, 38930696, 39026952, 39852552, 39864840, 39916040, 39961096, 40376832, 40900616, 41043976, 41226248, 41402376, 41433088]
def chunk7 : List ℕ := [41946017, 41953696, 41962144, 41969824, 41976609, 42009504, 42017184, 42025632, 42042144, 42076545, 42084736, 42205345, 42295456, 42469921, 42486304, 42500641, 42582560, 42993953, 43002144, 43024673, 43098400, 43124993, 43517985, 43542560, 43810849, 43900960, 44042881, 44059264, 44173441, 44198016, 44567041, 45746177, 46140160, 47327488, 48777728, 49965056, 50336705, 50344384, 50348736, 50365249, 50402176, 50409856, 50463169, 50471360, 50495809, 50598081, 50606272, 50725057, 50749632, 50860609, 50889281, 51122241, 51281985, 51384577, 52433537, 52499072, 52695169, 52768896, 52957697, 54267905, 54530880, 54538560, 54559552, 54596352, 54698304, 55054912, 55099968, 55324736, 55500864, 55652608, 57217536, 58535936, 58721153, 58753793, 58786688, 58851713, 58925440, 59932929, 60818049, 60899968, 61210753, 61300864, 61374977, 62816257, 63013632, 64200960, 65651200, 67100672]

def isMono2Gate (g : Gate) : Bool :=
  (match g.op with
   | GateOp.and => true
   | GateOp.or => true
   | _ => false) &&
  decide (g.inputs.length ≤ 2)

lemma isMono2Gate_sound (g : Gate) (h : isMono2Gate g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  unfold isMono2Gate at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  cases hop : g.op with
  | and => left; rfl
  | or => right; rfl
  | not => simp [hop] at h
  | mod _ => simp [hop] at h
  | maj => simp [hop] at h

lemma monotone2_C0 : PEqualNP.MetaComplexity.Monotone2 C0 := by
  have h : C0.gates.all isMono2Gate = true := by decide
  intro g hg
  exact isMono2Gate_sound g (List.all_eq_true.mp h g hg)

lemma size_C0 : C0.size = 64 := rfl

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD, List.getElem?_append_left hi]

lemma wstep_getD_eq (w : List Bool) (g : Gate) :
    (wstep w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [wstep, List.getD]

lemma foldl_wstep_spec (gs : List Gate) :
    ∀ (w : List Bool) (val : ℕ → Bool),
      (∀ i < w.length, w.getD i false = val i) →
      (∀ (k : ℕ) (hk : k < gs.length),
        val (w.length + k) = (gs[k]).op.eval ((gs[k]).inputs.map val) ∧
        ∀ j ∈ (gs[k]).inputs, j < w.length + k) →
      ∀ i < w.length + gs.length, (gs.foldl wstep w).getD i false = val i := by
  induction gs with
  | nil =>
    intro w val hinit _ i hi
    exact hinit i hi
  | cons g gs ih =>
    intro w val hinit hstep i hi
    rw [List.foldl_cons]
    have hg0 := hstep 0 (by simp)
    have hinit' : ∀ j < (wstep w g).length, (wstep w g).getD j false = val j := by
      intro j hj
      rw [wstep_len] at hj
      by_cases hlt : j < w.length
      · rw [wstep_getD_lt w g j hlt]
        exact hinit j hlt
      · have heq : j = w.length := by omega
        subst heq
        rw [wstep_getD_eq]
        have hmap : (g.inputs.map fun idx => w.getD idx false) = g.inputs.map val := by
          apply List.map_congr_left
          intro idx hidx
          exact hinit idx (hg0.2 idx hidx)
        rw [hmap]
        exact hg0.1.symm
    have hstep' : ∀ (k : ℕ) (hk : k < gs.length),
        val ((wstep w g).length + k) = (gs[k]).op.eval ((gs[k]).inputs.map val) ∧
        ∀ j ∈ (gs[k]).inputs, j < (wstep w g).length + k := by
      intro k hk
      have hk' : k + 1 < (g :: gs).length := by simp; omega
      have hs := hstep (k + 1) hk'
      rw [wstep_len]
      have hidx : w.length + 1 + k = w.length + (k + 1) := by omega
      rw [hidx]
      exact hs
    have hi' : i < (wstep w g).length + gs.length := by
      rw [wstep_len]
      simp only [List.length_cons] at hi
      omega
    exact ih (wstep w g) val hinit' hstep' i hi'

def rowVal (x : Fin 26 → Bool) (r : ℕ) : Bool :=
  if h : r < 13 then
    x ⟨13 + (13 - r) % 13, by omega⟩ &&
      ((x ⟨r, by omega⟩ || x ⟨(r + 1) % 13, by omega⟩) ||
       (x ⟨(r + 3) % 13, by omega⟩ || x ⟨(r + 9) % 13, by omega⟩))
  else false

def prefixOr (x : Fin 26 → Bool) : ℕ → Bool
  | 0 => rowVal x 0
  | n + 1 => prefixOr x n || rowVal x (n + 1)

def wireVal (x : Fin 26 → Bool) (k : ℕ) : Bool :=
  if h0 : k < 26 then x ⟨k, h0⟩
  else if h1 : k < 39 then
    x ⟨k - 26, by omega⟩ || x ⟨(k - 26 + 1) % 13, by omega⟩
  else if h2 : k < 52 then
    x ⟨k - 39, by omega⟩ || x ⟨(k - 39 + 6) % 13, by omega⟩
  else if h3 : k < 65 then
    (x ⟨k - 52, by omega⟩ || x ⟨(k - 52 + 1) % 13, by omega⟩) ||
    (x ⟨(k - 52 + 3) % 13, by omega⟩ || x ⟨(k - 52 + 9) % 13, by omega⟩)
  else if h4 : k < 78 then
    rowVal x (k - 65)
  else if h5 : k < 90 then
    prefixOr x (k - 77)
  else false

lemma C0_reads_back :
    ∀ k : Fin C0.gates.length, ∀ j ∈ (C0.gates[k.val]).inputs, j < 26 + k.val := by
  decide

set_option maxHeartbeats 800000 in
lemma C0_gate_eq (x : Fin 26 → Bool) (k : ℕ) (hk : k < C0.gates.length) :
    wireVal x (26 + k) = (C0.gates[k]).op.eval ((C0.gates[k]).inputs.map (wireVal x)) := by
  have hk64 : k < 64 := hk
  interval_cases k <;> simp [C0, wireVal, rowVal, prefixOr, eval_or2, eval_and2]

lemma eval_C0_eq_prefixOr (x : Fin 26 → Bool) :
    C0.eval (List.ofFn x) = prefixOr x 12 := by
  have hspec : ∀ i < (List.ofFn x).length + C0.gates.length,
      (C0.gates.foldl wstep (List.ofFn x)).getD i false = wireVal x i := by
    apply foldl_wstep_spec C0.gates (List.ofFn x) (wireVal x)
    · intro i hi
      simp only [List.length_ofFn] at hi
      rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
      simp [wireVal, hi]
    · intro k hk
      simp only [List.length_ofFn]
      exact ⟨C0_gate_eq x k hk, C0_reads_back ⟨k, hk⟩⟩
  have h89 := hspec 89 (by simp [C0])
  simpa [Circuit.eval, Circuit.wires, C0, wstep, wireVal] using h89

lemma prefixOr_eq_true_iff (x : Fin 26 → Bool) :
    ∀ n : ℕ, prefixOr x n = true ↔ ∃ r ≤ n, rowVal x r = true := by
  intro n
  induction n with
  | zero =>
    simp [prefixOr]
  | succ n ih =>
    simp only [prefixOr, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨r, hr, hrv⟩ | hrv)
      · exact ⟨r, by omega, hrv⟩
      · exact ⟨n + 1, le_refl _, hrv⟩
    · rintro ⟨r, hr, hrv⟩
      by_cases heq : r = n + 1
      · right; subst heq; exact hrv
      · left; exact ⟨r, by omega, hrv⟩

lemma eval_C0_true_of_inc (p l : Fin 13)
    (hinc : (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) :
    C0.eval (List.ofFn (fun i : Fin 26 => decide (i.val = p.val ∨ i.val = 13 + l.val))) = true := by
  rw [eval_C0_eq_prefixOr, prefixOr_eq_true_iff]
  refine ⟨(13 - l.val) % 13, by omega, ?_⟩
  have hlt : (13 - l.val) % 13 < 13 := by omega
  have hback : (13 - (13 - l.val) % 13) % 13 = l.val := by omega
  have hpl :
      p.val = (13 - l.val) % 13 ∨
      p.val = ((13 - l.val) % 13 + 1) % 13 ∨
      p.val = ((13 - l.val) % 13 + 3) % 13 ∨
      p.val = ((13 - l.val) % 13 + 9) % 13 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hinc
    omega
  simp only [rowVal, hlt, dite_true, hback, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨Or.inr trivial, ?_⟩
  rcases hpl with hp | hp | hp | hp
  · left; left; left; exact hp.symm
  · left; right; left; exact hp.symm
  · right; left; left; exact hp.symm
  · right; right; left; exact hp.symm

lemma eval_C0_false_of_nonInc (x : Fin 26 → Bool)
    (h : ∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
      ¬ (x ⟨p.val, by omega⟩ = true ∧ x ⟨13 + l.val, by omega⟩ = true)) :
    C0.eval (List.ofFn x) = false := by
  cases hev : C0.eval (List.ofFn x) with
  | false => rfl
  | true =>
    exfalso
    rw [eval_C0_eq_prefixOr, prefixOr_eq_true_iff] at hev
    rcases hev with ⟨r, hr, hrv⟩
    have hr13 : r < 13 := by omega
    simp only [rowVal, hr13, dite_true, Bool.and_eq_true, Bool.or_eq_true] at hrv
    rcases hrv with ⟨hl, (hp | hp) | (hp | hp)⟩
    · exact h ⟨r, hr13⟩ ⟨(13 - r) % 13, by omega⟩ (by
        have : (r + (13 - r) % 13) % 13 = 0 := by omega
        simp [this]) ⟨hp, hl⟩
    · exact h ⟨(r + 1) % 13, by omega⟩ ⟨(13 - r) % 13, by omega⟩ (by
        have : ((r + 1) % 13 + (13 - r) % 13) % 13 = 1 := by omega
        simp [this]) ⟨hp, hl⟩
    · exact h ⟨(r + 3) % 13, by omega⟩ ⟨(13 - r) % 13, by omega⟩ (by
        have : ((r + 3) % 13 + (13 - r) % 13) % 13 = 3 := by omega
        simp [this]) ⟨hp, hl⟩
    · exact h ⟨(r + 9) % 13, by omega⟩ ⟨(13 - r) % 13, by omega⟩ (by
        have : ((r + 9) % 13 + (13 - r) % 13) % 13 = 9 := by omega
        simp [this]) ⟨hp, hl⟩

def checkLine (m l mask : ℕ) : Bool :=
  !(m.testBit (13 + l)) || ((m &&& mask) == 0)

def checkM (m : ℕ) : Bool :=
  checkLine m 0 523 &&
  checkLine m 1 4357 &&
  checkLine m 2 6274 &&
  checkLine m 3 3137 &&
  checkLine m 4 5664 &&
  checkLine m 5 2832 &&
  checkLine m 6 1416 &&
  checkLine m 7 708 &&
  checkLine m 8 354 &&
  checkLine m 9 177 &&
  checkLine m 10 4184 &&
  checkLine m 11 2092 &&
  checkLine m 12 1046

lemma checkLine_sound (m l mask p : ℕ) (hc : checkLine m l mask = true)
    (hm : mask.testBit p = true) :
    ¬ (m.testBit p = true ∧ m.testBit (13 + l) = true) := by
  intro ⟨hp, hl⟩
  simp only [checkLine, hl, Bool.not_true, Bool.false_or, beq_iff_eq] at hc
  have h0 : (m &&& mask).testBit p = false := by rw [hc, Nat.zero_testBit]
  rw [Nat.testBit_and, hp, hm] at h0
  exact Bool.noConfusion h0

lemma checkM_sound (m : ℕ) (hc : checkM m = true) :
    ∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
      ¬ (Nat.testBit m p.val = true ∧ Nat.testBit m (13 + l.val) = true) := by
  unfold checkM at hc
  simp only [Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
  intro p l hinc
  have hpl :
      p.val = (13 - l.val) % 13 ∨ p.val = (14 - l.val) % 13 ∨
      p.val = (16 - l.val) % 13 ∨ p.val = (22 - l.val) % 13 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hinc
    omega
  fin_cases l
  · exact checkLine_sound m 0 523 p.val h0 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 1 4357 p.val h1 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 2 6274 p.val h2 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 3 3137 p.val h3 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 4 5664 p.val h4 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 5 2832 p.val h5 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 6 1416 p.val h6 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 7 708 p.val h7 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 8 354 p.val h8 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 9 177 p.val h9 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 10 4184 p.val h10 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 11 2092 p.val h11 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)
  · exact checkLine_sound m 12 1046 p.val h12 (by rcases hpl with hp | hp | hp | hp <;> simp [hp] <;> decide)

lemma check_chunk0 : chunk0.all checkM = true := rfl
lemma check_chunk1 : chunk1.all checkM = true := rfl
lemma check_chunk2 : chunk2.all checkM = true := rfl
lemma check_chunk3 : chunk3.all checkM = true := rfl
lemma check_chunk4 : chunk4.all checkM = true := rfl
lemma check_chunk5 : chunk5.all checkM = true := rfl
lemma check_chunk6 : chunk6.all checkM = true := rfl
lemma check_chunk7 : chunk7.all checkM = true := rfl

set_option maxRecDepth 4000 in
lemma nonIncList_eq :
    nonIncList = chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 := rfl

lemma checkAll_true : nonIncList.all checkM = true := by
  rw [nonIncList_eq]
  simp only [List.all_append, check_chunk0, check_chunk1, check_chunk2, check_chunk3,
    check_chunk4, check_chunk5, check_chunk6, check_chunk7, Bool.and_self]

lemma all_nonInc_and_false :
    ∀ m ∈ nonIncList,
      (∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
        ¬ (Nat.testBit m p.val = true ∧ Nat.testBit m (13 + l.val) = true)) ∧
      C0.eval (List.ofFn (fun j : Fin 26 => Nat.testBit m j.val)) = false := by
  intro m hm
  have hni := checkM_sound m (List.all_eq_true.mp checkAll_true m hm)
  refine ⟨hni, eval_C0_false_of_nonInc (fun j : Fin 26 => Nat.testBit m j.val) hni⟩

end PEqualNP.Outside.L_meta_1730

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_meta_1730 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 49]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 52]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 53]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 54]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 61]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [65, 66]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [78, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [79, 68]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [80, 69]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [81, 70]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [82, 71]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [83, 72]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [84, 73]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [85, 74]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [86, 75]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [87, 76]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [88, 77]⟩], output := 89 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 64 ∧ (∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) → C.eval (List.ofFn (fun i : Fin 26 => decide (i.val = p.val ∨ i.val = 13 + l.val))) = true) ∧ (∀ m ∈ ([8191, 15860, 20218, 27888, 34685, 42356, 50808, 58480, 70590, 78260, 82618, 90288, 99132, 106804, 115256, 133599, 141780, 149722, 157904, 164189, 172372, 180312, 197022, 205204, 213146, 229660, 237844, 267503, 275684, 279786, 287968, 296045, 304228, 312424, 320608, 331950, 340132, 344234, 360492, 393423, 401604, 409802, 426061, 458894, 475274, 531063, 538740, 543346, 551024, 557685, 565364, 574064, 581744, 594486, 602164, 606770, 623156, 630836, 639536, 657495, 665684, 673874, 682064, 688213, 696404, 720918, 790631, 798820, 802914, 819301, 827492, 856102, 864292, 917575, 950341, 1056059, 1064240, 1068090, 1076272, 1082681, 1090864, 1098808, 1106992, 1118522, 1126704, 1130554, 1147192, 1155376, 1163320, 1181979, 1190160, 1198106, 1212697, 1245466, 1261594, 1278232, 1315883, 1324064, 1328170, 1344553, 1360936, 1380394, 1392682, 1441803, 1579059, 1587248, 1591346, 1599536, 1605681, 1642546, 1650736, 1654834, 1695792, 1706003, 1722386, 1839139, 1904674, 2104989, 2112660, 2117272, 2124944, 2131485, 2139156, 2147864, 2167452, 2175124, 2179736, 2195996, 2212376, 2230429, 2238612, 2246808, 2254992, 2261021, 2293916, 2302100, 2310296, 2326556, 2364557, 2372740, 2376840, 2393101, 2429068, 2437252, 2490509, 2523149, 2556044, 2628117, 2635796, 2640400, 2654741, 2691604, 2699284, 2720276, 2754581, 2762772, 2785301, 2859028, 2887685, 3152921, 3161104, 3165208, 3173392, 3179545, 3195928, 3215384, 3278873, 3295256, 3309593, 3391512, 3413001, 3441673, 3676177, 3684368, 3803153, 3827728, 4202318, 4209988, 4214346, 4222016, 4228940, 4236612, 4245064, 4264718, 4272388, 4276746, 4293388, 4327758, 4335940, 4343882, 4358476, 4366660, 4391182, 4423948, 4461646, 4469828, 4473930, 4490316, 4498500, 4506696, 4526094, 4587598, 4603978, 4620364, 4653070, 4725318, 4732996, 4737602, 4751940, 4788742, 4851782, 4859972, 4868162, 4984902, 4993092, 5050374, 5111878, 5152836, 5250314, 5258496, 5262346, 5276936, 5312778, 5376266, 5392394, 5439754, 5510154, 5522442, 5574666, 5718026, 5773314, 6299148, 6306820, 6311432, 6325772, 6342152, 6361612, 6390284, 6424588, 6558732, 6566916, 6587404, 6623244, 6782988, 6822404, 6830084, 6885892, 7155716, 7347208, 7355392, 7359496, 7607304, 7652360, 8392615, 8400292, 8408738, 8416416, 8423205, 8430884, 8439328, 8455078, 8462756, 8471202, 8487716, 8495396, 8522119, 8530308, 8538242, 8552709, 8585606, 8593796, 8651943, 8660132, 8668322, 8676512, 8684581, 8692772, 8716454, 8724644, 8732834, 8781959, 8847494, 8915495, 8923172, 8931874, 8946213, 8978982, 8995362, 9011748, 9046023, 9175079, 9207845, 9240614, 9281572, 9306119, 9440547, 9448736, 9456674, 9464864, 9471265, 9479456, 9503010, 9570563, 9700387, 9716770, 9733153, 9757728, 9963555, 9979938, 10094595, 10223651, 10305570, 10489477, 10497156, 10505856, 10513536, 10520069, 10551940, 10619013, 10627204, 10749061, 10757252, 10781701, 10879109, 10952836, 11012613, 11043333, 11143173, 11436037, 11537409, 12586758, 12594436, 12602882, 12617476, 12625156, 12649222, 12681988, 12716294, 12724484, 12779782, 12820740, 12846086, 13109766, 13126146, 13173254, 13240326, 13565958, 13634818, 13643008, 13650946, 13764866, 14305282, 14683652, 14691332, 14700032, 14714372, 14984196, 15206916, 15303172, 15345668, 15704068, 15756288, 16783315, 16790992, 16795346, 16803024, 16811857, 16819536, 16827984, 16835664, 16847762, 16855440, 16859794, 16876304, 16908755, 16916944, 16924882, 16933072, 16941393, 16949584, 16974226, 16982416, 16990354, 17044675, 17052864, 17056962, 17065152, 17073217, 17109122, 17170627, 17187010, 17306195, 17313872, 17318482, 17334865, 17351248, 17371666, 17383954, 17432659, 17449042, 17465425, 17490000, 17567811, 17694787, 17831187, 17839376, 17843218, 17859857, 17868048, 17895698, 17903888, 17957139, 17989905, 18022674, 18063632, 18093059, 18354195, 18419730, 18481171, 18563090, 18616323, 18880145, 18887824, 18892432, 18900112, 18908689, 18925072, 18944656, 18952336, 18956944, 19005585, 19095696, 19141761, 19149952, 19403281, 19431953, 19468816, 19513872, 19928081, 19936272, 19956753, 19981328, 20190209, 20451345, 20525072, 20611089, 20701200, 20977474, 20985152, 20989506, 21006144, 21013824, 21022272, 21041922, 21102914, 21238850, 21247040, 21251138, 21292096, 21500482, 21512770, 21565954, 21762114, 21905474, 22025474, 22033664, 22089986, 22287362, 22876162, 23074304, 24392704, 25167747, 25175424, 25183874, 25200385, 25232258, 25248386, 25297283, 25362818, 25429123, 25445506, 25559171, 25641090, 25690627, 26215683, 26248449, 26345731, 26477571, 27131907, 27264641, 27281024, 27297281, 27526273, 27550848, 28607489, 29361922, 29378050, 29394688, 29426434, 29966850, 30409986, 30450944, 30605570, 30688258, 31408130, 31507968, 32826368, 33561577, 33569248, 33573608, 33581280, 33588073, 33595744, 33604200, 33625000, 33632672, 33637032, 33653544, 33669672, 33688009, 33696192, 33704136, 33712320, 33718601, 33751432, 33820905, 33829088, 33833192, 33841376, 33849449, 33865832, 33886376, 33894560, 33898664, 33947849, 33964232, 33980489, 34085473, 34093152, 34097760, 34105440, 34112097, 34128480, 34148896, 34211905, 34345057, 34353248, 34373729, 34398304, 34609449, 34617632, 34621480, 34636073, 34672936, 34681120, 34701608, 34736393, 34767113, 34869289, 34897961, 34934824, 34979880, 35133473, 35141664, 35393569, 35467296, 35658377, 35666048, 35670664, 35684873, 35721864, 35734152, 35784841, 35801224, 35917961, 35983496, 36044937, 36126856, 36182529, 36706313, 36833289, 36966409, 37126153, 37230593, 37755720, 37763392, 37767752, 37782344, 37798472, 37819144, 37847816, 37882184, 37890368, 37898312, 37912904, 38015048, 38191176, 38279744, 38287424, 38292032, 38430784, 38803720, 38811904, 38867208, 38930696, 39026952, 39852552, 39864840, 39916040, 39961096, 40376832, 40900616, 41043976, 41226248, 41402376, 41433088, 41946017, 41953696, 41962144, 41969824, 41976609, 42009504, 42017184, 42025632, 42042144, 42076545, 42084736, 42205345, 42295456, 42469921, 42486304, 42500641, 42582560, 42993953, 43002144, 43024673, 43098400, 43124993, 43517985, 43542560, 43810849, 43900960, 44042881, 44059264, 44173441, 44198016, 44567041, 45746177, 46140160, 47327488, 48777728, 49965056, 50336705, 50344384, 50348736, 50365249, 50402176, 50409856, 50463169, 50471360, 50495809, 50598081, 50606272, 50725057, 50749632, 50860609, 50889281, 51122241, 51281985, 51384577, 52433537, 52499072, 52695169, 52768896, 52957697, 54267905, 54530880, 54538560, 54559552, 54596352, 54698304, 55054912, 55099968, 55324736, 55500864, 55652608, 57217536, 58535936, 58721153, 58753793, 58786688, 58851713, 58925440, 59932929, 60818049, 60899968, 61210753, 61300864, 61374977, 62816257, 63013632, 64200960, 65651200, 67100672] : List ℕ), (∀ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) → ¬ (Nat.testBit m p.val = true ∧ Nat.testBit m (13 + l.val) = true)) ∧ C.eval (List.ofFn (fun j : Fin 26 => Nat.testBit m j.val)) = false) := by
  intro C hC
  subst hC
  exact ⟨PEqualNP.Outside.L_meta_1730.monotone2_C0,
    PEqualNP.Outside.L_meta_1730.size_C0,
    PEqualNP.Outside.L_meta_1730.eval_C0_true_of_inc,
    PEqualNP.Outside.L_meta_1730.all_nonInc_and_false⟩
