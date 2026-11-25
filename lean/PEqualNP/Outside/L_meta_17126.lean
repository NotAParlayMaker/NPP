import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17126
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def v15 (x : Fin 15 → Bool) : Bool := x 0 && (x 1 && true)
def v16 (x : Fin 15 → Bool) : Bool := x 2 && (x 3 && true)
def v17 (x : Fin 15 → Bool) : Bool := x 4 && (x 5 && true)
def v18 (x : Fin 15 → Bool) : Bool := x 6 && (x 7 && true)
def v19 (x : Fin 15 → Bool) : Bool := x 8 && (x 9 && true)
def v20 (x : Fin 15 → Bool) : Bool := x 10 && (x 11 && true)
def v21 (x : Fin 15 → Bool) : Bool := x 12 && (x 13 && true)
def v22 (x : Fin 15 → Bool) : Bool := x 14 && (v20 x && true)
def v23 (x : Fin 15 → Bool) : Bool := x 14 && (v21 x && true)
def v24 (x : Fin 15 → Bool) : Bool := v16 x && (v19 x && true)
def v25 (x : Fin 15 → Bool) : Bool := v17 x && (v18 x && true)
def v26 (x : Fin 15 → Bool) : Bool := x 3 && (v19 x && true)
def v27 (x : Fin 15 → Bool) : Bool := x 5 && (v15 x && true)
def v28 (x : Fin 15 → Bool) : Bool := v15 x && (v17 x && true)
def v29 (x : Fin 15 → Bool) : Bool := x 2 && (x 9 && true)
def v30 (x : Fin 15 → Bool) : Bool := x 4 && (x 13 && true)
def v31 (x : Fin 15 → Bool) : Bool := x 2 && (x 8 && true)
def v32 (x : Fin 15 → Bool) : Bool := x 11 && (v18 x && true)
def v33 (x : Fin 15 → Bool) : Bool := x 0 && (v22 x && true)
def v34 (x : Fin 15 → Bool) : Bool := x 1 && (v23 x && true)
def v35 (x : Fin 15 → Bool) : Bool := x 2 && (v19 x && true)
def v36 (x : Fin 15 → Bool) : Bool := x 4 && (v15 x && true)
def v37 (x : Fin 15 → Bool) : Bool := x 7 && (x 10 && true)
def v38 (x : Fin 15 → Bool) : Bool := x 8 && (v16 x && true)
def v39 (x : Fin 15 → Bool) : Bool := x 12 && (x 14 && true)
def v40 (x : Fin 15 → Bool) : Bool := x 1 && (v22 x && true)
def v41 (x : Fin 15 → Bool) : Bool := x 6 && (x 10 && true)
def v42 (x : Fin 15 → Bool) : Bool := x 7 && (x 11 && true)
def v43 (x : Fin 15 → Bool) : Bool := x 9 && (v16 x && true)
def v44 (x : Fin 15 → Bool) : Bool := x 13 && (x 14 && true)
def v45 (x : Fin 15 → Bool) : Bool := x 0 && (v20 x && true)
def v46 (x : Fin 15 → Bool) : Bool := x 0 && (v23 x && true)
def v47 (x : Fin 15 → Bool) : Bool := x 1 && (v20 x && true)
def v48 (x : Fin 15 → Bool) : Bool := x 3 && (x 9 && true)
def v49 (x : Fin 15 → Bool) : Bool := x 4 && (v18 x && true)
def v50 (x : Fin 15 → Bool) : Bool := x 5 && (x 6 && true)
def v51 (x : Fin 15 → Bool) : Bool := x 6 && (v22 x && true)
def v52 (x : Fin 15 → Bool) : Bool := x 10 && (v25 x && true)
def v53 (x : Fin 15 → Bool) : Bool := x 0 && (x 14 && true)
def v54 (x : Fin 15 → Bool) : Bool := x 1 && (x 10 && true)
def v55 (x : Fin 15 → Bool) : Bool := x 3 && (x 8 && true)
def v56 (x : Fin 15 → Bool) : Bool := x 5 && (x 7 && true)
def v57 (x : Fin 15 → Bool) : Bool := x 12 && (v18 x && true)
def v58 (x : Fin 15 → Bool) : Bool := x 12 && (v25 x && true)
def v59 (x : Fin 15 → Bool) : Bool := v15 x && (v23 x && true)
def v60 (x : Fin 15 → Bool) : Bool := v16 x && (v28 x && true)
def v61 (x : Fin 15 → Bool) : Bool := v17 x && (v24 x && true)
def v62 (x : Fin 15 → Bool) : Bool := v17 x && (v46 x && true)
def v63 (x : Fin 15 → Bool) : Bool := x 0 && (v26 x && true)
def v64 (x : Fin 15 → Bool) : Bool := x 1 && (v30 x && true)
def v65 (x : Fin 15 → Bool) : Bool := x 5 && (v38 x && true)
def v66 (x : Fin 15 → Bool) : Bool := x 6 && (x 11 && true)
def v67 (x : Fin 15 → Bool) : Bool := x 6 && (x 12 && true)
def v68 (x : Fin 15 → Bool) : Bool := x 6 && (v30 x && true)
def v69 (x : Fin 15 → Bool) : Bool := x 7 && (x 12 && true)
def v70 (x : Fin 15 → Bool) : Bool := x 7 && (v28 x && true)
def v71 (x : Fin 15 → Bool) : Bool := x 8 && (v21 x && true)
def v72 (x : Fin 15 → Bool) : Bool := x 9 && (v21 x && true)
def v73 (x : Fin 15 → Bool) : Bool := x 11 && (v43 x && true)
def v74 (x : Fin 15 → Bool) : Bool := x 13 && (v27 x && true)
def v75 (x : Fin 15 → Bool) : Bool := x 13 && (v47 x && true)
def v76 (x : Fin 15 → Bool) : Bool := x 14 && (v32 x && true)
def v77 (x : Fin 15 → Bool) : Bool := v15 x && (v18 x && true)
def v78 (x : Fin 15 → Bool) : Bool := v17 x && (v31 x && true)
def v79 (x : Fin 15 → Bool) : Bool := v17 x && (v47 x && true)
def v80 (x : Fin 15 → Bool) : Bool := v18 x && (v27 x && true)
def v81 (x : Fin 15 → Bool) : Bool := v21 x && (v24 x && true)
def v82 (x : Fin 15 → Bool) : Bool := v21 x && (v27 x && true)
def v83 (x : Fin 15 → Bool) : Bool := v21 x && (v33 x && true)
def v84 (x : Fin 15 → Bool) : Bool := v21 x && (v49 x && true)
def v85 (x : Fin 15 → Bool) : Bool := v24 x && (v36 x && true)
def v86 (x : Fin 15 → Bool) : Bool := v24 x && (v50 x && true)
def v87 (x : Fin 15 → Bool) : Bool := v25 x && (v29 x && true)
def v88 (x : Fin 15 → Bool) : Bool := v44 x && (v80 x && true)
def v89 (x : Fin 15 → Bool) : Bool := x 0 && (v16 x && true)
def v90 (x : Fin 15 → Bool) : Bool := x 0 && (v31 x && true)
def v91 (x : Fin 15 → Bool) : Bool := x 1 && (v32 x && true)
def v92 (x : Fin 15 → Bool) : Bool := x 3 && (x 4 && true)
def v93 (x : Fin 15 → Bool) : Bool := x 3 && (v21 x && true)
def v94 (x : Fin 15 → Bool) : Bool := x 3 && (v27 x && true)
def v95 (x : Fin 15 → Bool) : Bool := x 3 && (v34 x && true)
def v96 (x : Fin 15 → Bool) : Bool := x 4 && (x 7 && true)
def v97 (x : Fin 15 → Bool) : Bool := x 4 && (v16 x && true)
def v98 (x : Fin 15 → Bool) : Bool := x 5 && (x 9 && true)
def v99 (x : Fin 15 → Bool) : Bool := x 5 && (v24 x && true)
def v100 (x : Fin 15 → Bool) : Bool := x 6 && (v27 x && true)
def v101 (x : Fin 15 → Bool) : Bool := x 6 && (v45 x && true)
def v102 (x : Fin 15 → Bool) : Bool := x 7 && (v22 x && true)
def v103 (x : Fin 15 → Bool) : Bool := x 7 && (v30 x && true)
def v104 (x : Fin 15 → Bool) : Bool := x 8 && (x 11 && true)
def v105 (x : Fin 15 → Bool) : Bool := x 8 && (v18 x && true)
def v106 (x : Fin 15 → Bool) : Bool := x 8 && (v22 x && true)
def v107 (x : Fin 15 → Bool) : Bool := x 9 && (x 12 && true)
def v108 (x : Fin 15 → Bool) : Bool := x 10 && (v21 x && true)
def v109 (x : Fin 15 → Bool) : Bool := x 10 && (v31 x && true)
def v110 (x : Fin 15 → Bool) : Bool := x 10 && (v57 x && true)
def v111 (x : Fin 15 → Bool) : Bool := x 11 && (x 13 && true)
def v112 (x : Fin 15 → Bool) : Bool := x 11 && (v26 x && true)
def v113 (x : Fin 15 → Bool) : Bool := x 11 && (v29 x && true)
def v114 (x : Fin 15 → Bool) : Bool := x 11 && (v58 x && true)
def v115 (x : Fin 15 → Bool) : Bool := x 12 && (v22 x && true)
def v116 (x : Fin 15 → Bool) : Bool := x 12 && (v33 x && true)
def v117 (x : Fin 15 → Bool) : Bool := x 12 && (v42 x && true)
def v118 (x : Fin 15 → Bool) : Bool := x 12 && (v43 x && true)
def v119 (x : Fin 15 → Bool) : Bool := x 13 && (v17 x && true)
def v120 (x : Fin 15 → Bool) : Bool := x 13 && (v18 x && true)
def v121 (x : Fin 15 → Bool) : Bool := x 13 && (v52 x && true)
def v122 (x : Fin 15 → Bool) : Bool := x 14 && (v41 x && true)
def v123 (x : Fin 15 → Bool) : Bool := v15 x && (v19 x && true)
def v124 (x : Fin 15 → Bool) : Bool := v15 x && (v24 x && true)
def v125 (x : Fin 15 → Bool) : Bool := v15 x && (v52 x && true)
def v126 (x : Fin 15 → Bool) : Bool := v16 x && (v20 x && true)
def v127 (x : Fin 15 → Bool) : Bool := v16 x && (v22 x && true)
def v128 (x : Fin 15 → Bool) : Bool := v16 x && (v56 x && true)
def v129 (x : Fin 15 → Bool) : Bool := v17 x && (v34 x && true)
def v130 (x : Fin 15 → Bool) : Bool := v18 x && (v30 x && true)
def v131 (x : Fin 15 → Bool) : Bool := v19 x && (v23 x && true)
def v132 (x : Fin 15 → Bool) : Bool := v19 x && (v50 x && true)
def v133 (x : Fin 15 → Bool) : Bool := v20 x && (v26 x && true)
def v134 (x : Fin 15 → Bool) : Bool := v20 x && (v36 x && true)
def v135 (x : Fin 15 → Bool) : Bool := v20 x && (v70 x && true)
def v136 (x : Fin 15 → Bool) : Bool := v21 x && (v25 x && true)
def v137 (x : Fin 15 → Bool) : Bool := v21 x && (v41 x && true)
def v138 (x : Fin 15 → Bool) : Bool := v21 x && (v42 x && true)
def v139 (x : Fin 15 → Bool) : Bool := v22 x && (v72 x && true)
def v140 (x : Fin 15 → Bool) : Bool := v22 x && (v77 x && true)
def v141 (x : Fin 15 → Bool) : Bool := v23 x && (v97 x && true)
def v142 (x : Fin 15 → Bool) : Bool := v23 x && (v105 x && true)
def v143 (x : Fin 15 → Bool) : Bool := v24 x && (v28 x && true)
def v144 (x : Fin 15 → Bool) : Bool := v24 x && (v33 x && true)
def v145 (x : Fin 15 → Bool) : Bool := v24 x && (v56 x && true)
def v146 (x : Fin 15 → Bool) : Bool := v25 x && (v39 x && true)
def v147 (x : Fin 15 → Bool) : Bool := v25 x && (v48 x && true)
def v148 (x : Fin 15 → Bool) : Bool := v26 x && (v33 x && true)
def v149 (x : Fin 15 → Bool) : Bool := v26 x && (v37 x && true)
def v150 (x : Fin 15 → Bool) : Bool := v26 x && (v39 x && true)
def v151 (x : Fin 15 → Bool) : Bool := v26 x && (v64 x && true)
def v152 (x : Fin 15 → Bool) : Bool := v26 x && (v67 x && true)
def v153 (x : Fin 15 → Bool) : Bool := v26 x && (v88 x && true)
def v154 (x : Fin 15 → Bool) : Bool := v27 x && (v31 x && true)
def v155 (x : Fin 15 → Bool) : Bool := v27 x && (v35 x && true)
def v156 (x : Fin 15 → Bool) : Bool := v28 x && (v38 x && true)
def v157 (x : Fin 15 → Bool) : Bool := v28 x && (v51 x && true)
def v158 (x : Fin 15 → Bool) : Bool := v28 x && (v104 x && true)
def v159 (x : Fin 15 → Bool) : Bool := v29 x && (v32 x && true)
def v160 (x : Fin 15 → Bool) : Bool := v29 x && (v41 x && true)
def v161 (x : Fin 15 → Bool) : Bool := v29 x && (v45 x && true)
def v162 (x : Fin 15 → Bool) : Bool := v29 x && (v74 x && true)
def v163 (x : Fin 15 → Bool) : Bool := v29 x && (v100 x && true)
def v164 (x : Fin 15 → Bool) : Bool := v30 x && (v37 x && true)
def v165 (x : Fin 15 → Bool) : Bool := v30 x && (v77 x && true)
def v166 (x : Fin 15 → Bool) : Bool := v31 x && (v40 x && true)
def v167 (x : Fin 15 → Bool) : Bool := v31 x && (v45 x && true)
def v168 (x : Fin 15 → Bool) : Bool := v32 x && (v39 x && true)
def v169 (x : Fin 15 → Bool) : Bool := v32 x && (v53 x && true)
def v170 (x : Fin 15 → Bool) : Bool := v32 x && (v55 x && true)
def v171 (x : Fin 15 → Bool) : Bool := v33 x && (v35 x && true)
def v172 (x : Fin 15 → Bool) : Bool := v34 x && (v37 x && true)
def v173 (x : Fin 15 → Bool) : Bool := v34 x && (v42 x && true)
def v174 (x : Fin 15 → Bool) : Bool := v34 x && (v86 x && true)
def v175 (x : Fin 15 → Bool) : Bool := v34 x && (v87 x && true)
def v176 (x : Fin 15 → Bool) : Bool := v35 x && (v41 x && true)
def v177 (x : Fin 15 → Bool) : Bool := v35 x && (v52 x && true)
def v178 (x : Fin 15 → Bool) : Bool := v35 x && (v54 x && true)
def v179 (x : Fin 15 → Bool) : Bool := v35 x && (v69 x && true)
def v180 (x : Fin 15 → Bool) : Bool := v36 x && (v42 x && true)
def v181 (x : Fin 15 → Bool) : Bool := v36 x && (v43 x && true)
def v182 (x : Fin 15 → Bool) : Bool := v36 x && (v51 x && true)
def v183 (x : Fin 15 → Bool) : Bool := v37 x && (v39 x && true)
def v184 (x : Fin 15 → Bool) : Bool := v37 x && (v48 x && true)
def v185 (x : Fin 15 → Bool) : Bool := v37 x && (v94 x && true)
def v186 (x : Fin 15 → Bool) : Bool := v38 x && (v40 x && true)
def v187 (x : Fin 15 → Bool) : Bool := v38 x && (v51 x && true)
def v188 (x : Fin 15 → Bool) : Bool := v38 x && (v67 x && true)
def v189 (x : Fin 15 → Bool) : Bool := v39 x && (v60 x && true)
def v190 (x : Fin 15 → Bool) : Bool := v39 x && (v143 x && true)
def v191 (x : Fin 15 → Bool) : Bool := v40 x && (v86 x && true)
def v192 (x : Fin 15 → Bool) : Bool := v40 x && (v87 x && true)
def v193 (x : Fin 15 → Bool) : Bool := v40 x && (v92 x && true)
def v194 (x : Fin 15 → Bool) : Bool := v41 x && (v44 x && true)
def v195 (x : Fin 15 → Bool) : Bool := v42 x && (v44 x && true)
def v196 (x : Fin 15 → Bool) : Bool := v43 x && (v44 x && true)
def v197 (x : Fin 15 → Bool) : Bool := v45 x && (v65 x && true)
def v198 (x : Fin 15 → Bool) : Bool := v46 x && (v50 x && true)
def v199 (x : Fin 15 → Bool) : Bool := v48 x && (v49 x && true)
def v200 (x : Fin 15 → Bool) : Bool := v48 x && (v51 x && true)
def v201 (x : Fin 15 → Bool) : Bool := v49 x && (v54 x && true)
def v202 (x : Fin 15 → Bool) : Bool := v52 x && (v95 x && true)
def v203 (x : Fin 15 → Bool) : Bool := v53 x && (v55 x && true)
def v204 (x : Fin 15 → Bool) : Bool := v53 x && (v177 x && true)
def v205 (x : Fin 15 → Bool) : Bool := v54 x && (v118 x && true)
def v206 (x : Fin 15 → Bool) : Bool := v55 x && (v66 x && true)
def v207 (x : Fin 15 → Bool) : Bool := v56 x && (v106 x && true)
def v208 (x : Fin 15 → Bool) : Bool := v57 x && (v89 x && true)
def v209 (x : Fin 15 → Bool) : Bool := v57 x && (v186 x && true)
def v210 (x : Fin 15 → Bool) : Bool := v58 x && (v127 x && true)
def v211 (x : Fin 15 → Bool) : Bool := v58 x && (v167 x && true)
def v212 (x : Fin 15 → Bool) : Bool := v59 x && (v149 x && true)
def v213 (x : Fin 15 → Bool) : Bool := v59 x && (v159 x && true)
def v214 (x : Fin 15 → Bool) : Bool := v59 x && (v176 x && true)
def v215 (x : Fin 15 → Bool) : Bool := v60 x && (v138 x && true)
def v216 (x : Fin 15 → Bool) : Bool := v60 x && (v194 x && true)
def v217 (x : Fin 15 → Bool) : Bool := v61 x && (v137 x && true)
def v218 (x : Fin 15 → Bool) : Bool := v61 x && (v183 x && true)
def v219 (x : Fin 15 → Bool) : Bool := v61 x && (v195 x && true)
def v220 (x : Fin 15 → Bool) : Bool := v62 x && (v112 x && true)
def v221 (x : Fin 15 → Bool) : Bool := v62 x && (v160 x && true)
def v222 (x : Fin 15 → Bool) : Bool := v62 x && (v184 x && true)
def v223 (x : Fin 15 → Bool) : Bool := v63 x && (v114 x && true)
def v224 (x : Fin 15 → Bool) : Bool := v63 x && (v121 x && true)
def v225 (x : Fin 15 → Bool) : Bool := v64 x && (v113 x && true)
def v226 (x : Fin 15 → Bool) : Bool := v65 x && (v172 x && true)
def v227 (x : Fin 15 → Bool) : Bool := v66 x && (v189 x && true)
def v228 (x : Fin 15 → Bool) : Bool := v68 x && (v90 x && true)
def v229 (x : Fin 15 → Bool) : Bool := v68 x && (v148 x && true)
def v230 (x : Fin 15 → Bool) : Bool := v69 x && (v144 x && true)
def v231 (x : Fin 15 → Bool) : Bool := v70 x && (v196 x && true)
def v232 (x : Fin 15 → Bool) : Bool := v71 x && (v125 x && true)
def v233 (x : Fin 15 → Bool) : Bool := v71 x && (v182 x && true)
def v234 (x : Fin 15 → Bool) : Bool := v72 x && (v135 x && true)
def v235 (x : Fin 15 → Bool) : Bool := v73 x && (v136 x && true)
def v236 (x : Fin 15 → Bool) : Bool := v73 x && (v198 x && true)
def v237 (x : Fin 15 → Bool) : Bool := v74 x && (v200 x && true)
def v238 (x : Fin 15 → Bool) : Bool := v75 x && (v145 x && true)
def v239 (x : Fin 15 → Bool) : Bool := v75 x && (v147 x && true)
def v240 (x : Fin 15 → Bool) : Bool := v76 x && (v151 x && true)
def v241 (x : Fin 15 → Bool) : Bool := v76 x && (v181 x && true)
def v242 (x : Fin 15 → Bool) : Bool := v78 x && (v83 x && true)
def v243 (x : Fin 15 → Bool) : Bool := v78 x && (v173 x && true)
def v244 (x : Fin 15 → Bool) : Bool := v79 x && (v152 x && true)
def v245 (x : Fin 15 → Bool) : Bool := v79 x && (v179 x && true)
def v246 (x : Fin 15 → Bool) : Bool := v81 x && (v91 x && true)
def v247 (x : Fin 15 → Bool) : Bool := v81 x && (v101 x && true)
def v248 (x : Fin 15 → Bool) : Bool := v82 x && (v133 x && true)
def v249 (x : Fin 15 → Bool) : Bool := v82 x && (v170 x && true)
def v250 (x : Fin 15 → Bool) : Bool := v83 x && (v128 x && true)
def v251 (x : Fin 15 → Bool) : Bool := v84 x && (v161 x && true)
def v252 (x : Fin 15 → Bool) : Bool := v84 x && (v178 x && true)
def v253 (x : Fin 15 → Bool) : Bool := v85 x && (v117 x && true)
def v254 (x : Fin 15 → Bool) : Bool := v85 x && (v122 x && true)
def v255 (x : Fin 15 → Bool) : Bool := v88 x && (v109 x && true)
def v256 (x : Fin 15 → Bool) : Bool := v93 x && (v140 x && true)
def v257 (x : Fin 15 → Bool) : Bool := v96 x && (v203 x && true)
def v258 (x : Fin 15 → Bool) : Bool := v98 x && (v110 x && true)
def v259 (x : Fin 15 → Bool) : Bool := v99 x && (v169 x && true)
def v260 (x : Fin 15 → Bool) : Bool := v102 x && (v162 x && true)
def v261 (x : Fin 15 → Bool) : Bool := v103 x && (v171 x && true)
def v262 (x : Fin 15 → Bool) : Bool := v107 x && (v157 x && true)
def v263 (x : Fin 15 → Bool) : Bool := v108 x && (v156 x && true)
def v264 (x : Fin 15 → Bool) : Bool := v111 x && (v132 x && true)
def v265 (x : Fin 15 → Bool) : Bool := v115 x && (v155 x && true)
def v266 (x : Fin 15 → Bool) : Bool := v116 x && (v199 x && true)
def v267 (x : Fin 15 → Bool) : Bool := v119 x && (v187 x && true)
def v268 (x : Fin 15 → Bool) : Bool := v120 x && (v197 x && true)
def v269 (x : Fin 15 → Bool) : Bool := v123 x && (v146 x && true)
def v270 (x : Fin 15 → Bool) : Bool := v124 x && (v164 x && true)
def v271 (x : Fin 15 → Bool) : Bool := v126 x && (v165 x && true)
def v272 (x : Fin 15 → Bool) : Bool := v129 x && (v206 x && true)
def v273 (x : Fin 15 → Bool) : Bool := v130 x && (v166 x && true)
def v274 (x : Fin 15 → Bool) : Bool := v131 x && (v180 x && true)
def v275 (x : Fin 15 → Bool) : Bool := v134 x && (v188 x && true)
def v276 (x : Fin 15 → Bool) : Bool := v150 x && (v201 x && true)
def v277 (x : Fin 15 → Bool) : Bool := v154 x && (v168 x && true)
def v278 (x : Fin 15 → Bool) : Bool := v231 x || (v228 x || false)
def v279 (x : Fin 15 → Bool) : Bool := v278 x || (v235 x || false)
def v280 (x : Fin 15 → Bool) : Bool := v279 x || (v222 x || false)
def v281 (x : Fin 15 → Bool) : Bool := v280 x || (v192 x || false)
def v282 (x : Fin 15 → Bool) : Bool := v281 x || (v213 x || false)
def v283 (x : Fin 15 → Bool) : Bool := v282 x || (v212 x || false)
def v284 (x : Fin 15 → Bool) : Bool := v283 x || (v239 x || false)
def v285 (x : Fin 15 → Bool) : Bool := v284 x || (v266 x || false)
def v286 (x : Fin 15 → Bool) : Bool := v285 x || (v237 x || false)
def v287 (x : Fin 15 → Bool) : Bool := v286 x || (v234 x || false)
def v288 (x : Fin 15 → Bool) : Bool := v287 x || (v217 x || false)
def v289 (x : Fin 15 → Bool) : Bool := v288 x || (v227 x || false)
def v290 (x : Fin 15 → Bool) : Bool := v289 x || (v233 x || false)
def v291 (x : Fin 15 → Bool) : Bool := v290 x || (v230 x || false)
def v292 (x : Fin 15 → Bool) : Bool := v291 x || (v238 x || false)
def v293 (x : Fin 15 → Bool) : Bool := v292 x || (v256 x || false)
def v294 (x : Fin 15 → Bool) : Bool := v293 x || (v245 x || false)
def v295 (x : Fin 15 → Bool) : Bool := v294 x || (v265 x || false)
def v296 (x : Fin 15 → Bool) : Bool := v295 x || (v261 x || false)
def v297 (x : Fin 15 → Bool) : Bool := v296 x || (v277 x || false)
def v298 (x : Fin 15 → Bool) : Bool := v297 x || (v248 x || false)
def v299 (x : Fin 15 → Bool) : Bool := v298 x || (v252 x || false)
def v300 (x : Fin 15 → Bool) : Bool := v299 x || (v218 x || false)
def v301 (x : Fin 15 → Bool) : Bool := v300 x || (v236 x || false)
def v302 (x : Fin 15 → Bool) : Bool := v301 x || (v241 x || false)
def v303 (x : Fin 15 → Bool) : Bool := v302 x || (v255 x || false)
def v304 (x : Fin 15 → Bool) : Bool := v303 x || (v185 x || false)
def v305 (x : Fin 15 → Bool) : Bool := v304 x || (v229 x || false)
def v306 (x : Fin 15 → Bool) : Bool := v305 x || (v271 x || false)
def v307 (x : Fin 15 → Bool) : Bool := v306 x || (v139 x || false)
def v308 (x : Fin 15 → Bool) : Bool := v307 x || (v210 x || false)
def v309 (x : Fin 15 → Bool) : Bool := v308 x || (v163 x || false)
def v310 (x : Fin 15 → Bool) : Bool := v309 x || (v219 x || false)
def v311 (x : Fin 15 → Bool) : Bool := v310 x || (v226 x || false)
def v312 (x : Fin 15 → Bool) : Bool := v311 x || (v190 x || false)
def v313 (x : Fin 15 → Bool) : Bool := v312 x || (v270 x || false)
def v314 (x : Fin 15 → Bool) : Bool := v313 x || (v232 x || false)
def v315 (x : Fin 15 → Bool) : Bool := v314 x || (v251 x || false)
def v316 (x : Fin 15 → Bool) : Bool := v315 x || (v202 x || false)
def v317 (x : Fin 15 → Bool) : Bool := v316 x || (v243 x || false)
def v318 (x : Fin 15 → Bool) : Bool := v317 x || (v240 x || false)
def v319 (x : Fin 15 → Bool) : Bool := v318 x || (v242 x || false)
def v320 (x : Fin 15 → Bool) : Bool := v319 x || (v244 x || false)
def v321 (x : Fin 15 → Bool) : Bool := v320 x || (v257 x || false)
def v322 (x : Fin 15 → Bool) : Bool := v321 x || (v209 x || false)
def v323 (x : Fin 15 → Bool) : Bool := v322 x || (v267 x || false)
def v324 (x : Fin 15 → Bool) : Bool := v323 x || (v253 x || false)
def v325 (x : Fin 15 → Bool) : Bool := v324 x || (v208 x || false)
def v326 (x : Fin 15 → Bool) : Bool := v325 x || (v263 x || false)
def v327 (x : Fin 15 → Bool) : Bool := v326 x || (v272 x || false)
def v328 (x : Fin 15 → Bool) : Bool := v327 x || (v249 x || false)
def v329 (x : Fin 15 → Bool) : Bool := v328 x || (v276 x || false)
def v330 (x : Fin 15 → Bool) : Bool := v329 x || (v224 x || false)
def v331 (x : Fin 15 → Bool) : Bool := v330 x || (v211 x || false)
def v332 (x : Fin 15 → Bool) : Bool := v331 x || (v204 x || false)
def v333 (x : Fin 15 → Bool) : Bool := v332 x || (v214 x || false)
def v334 (x : Fin 15 → Bool) : Bool := v333 x || (v262 x || false)
def v335 (x : Fin 15 → Bool) : Bool := v334 x || (v215 x || false)
def v336 (x : Fin 15 → Bool) : Bool := v335 x || (v191 x || false)
def v337 (x : Fin 15 → Bool) : Bool := v336 x || (v158 x || false)
def v338 (x : Fin 15 → Bool) : Bool := v337 x || (v205 x || false)
def v339 (x : Fin 15 → Bool) : Bool := v338 x || (v274 x || false)
def v340 (x : Fin 15 → Bool) : Bool := v339 x || (v254 x || false)
def v341 (x : Fin 15 → Bool) : Bool := v340 x || (v275 x || false)
def v342 (x : Fin 15 → Bool) : Bool := v341 x || (v268 x || false)
def v343 (x : Fin 15 → Bool) : Bool := v342 x || (v260 x || false)
def v344 (x : Fin 15 → Bool) : Bool := v343 x || (v207 x || false)
def v345 (x : Fin 15 → Bool) : Bool := v344 x || (v153 x || false)
def v346 (x : Fin 15 → Bool) : Bool := v345 x || (v141 x || false)
def v347 (x : Fin 15 → Bool) : Bool := v346 x || (v142 x || false)
def v348 (x : Fin 15 → Bool) : Bool := v347 x || (v273 x || false)
def v349 (x : Fin 15 → Bool) : Bool := v348 x || (v250 x || false)
def v350 (x : Fin 15 → Bool) : Bool := v349 x || (v264 x || false)
def v351 (x : Fin 15 → Bool) : Bool := v350 x || (v259 x || false)
def v352 (x : Fin 15 → Bool) : Bool := v351 x || (v216 x || false)
def v353 (x : Fin 15 → Bool) : Bool := v352 x || (v246 x || false)
def v354 (x : Fin 15 → Bool) : Bool := v353 x || (v193 x || false)
def v355 (x : Fin 15 → Bool) : Bool := v354 x || (v247 x || false)
def v356 (x : Fin 15 → Bool) : Bool := v355 x || (v225 x || false)
def v357 (x : Fin 15 → Bool) : Bool := v356 x || (v258 x || false)
def v358 (x : Fin 15 → Bool) : Bool := v357 x || (v223 x || false)
def v359 (x : Fin 15 → Bool) : Bool := v358 x || (v174 x || false)
def v360 (x : Fin 15 → Bool) : Bool := v359 x || (v269 x || false)
def v361 (x : Fin 15 → Bool) : Bool := v360 x || (v220 x || false)
def v362 (x : Fin 15 → Bool) : Bool := v361 x || (v221 x || false)
def v363 (x : Fin 15 → Bool) : Bool := v362 x || (v175 x || false)
def v364 (x : Fin 15 → Bool) : Bool := !(v363 x)

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Trace (t : ℕ → Bool) : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs => g.op.eval (g.inputs.map fun i => if i < n then t i else false) = t n ∧ Trace t (n+1) gs

theorem trace_sound (t : ℕ → Bool) (gs : List Gate) (n : ℕ) (W : List Bool)
    (len : W.length = n) (read : ∀ i, W.getD i false = if i < n then t i else false)
    (ok : Trace t n gs) :
    ∀ i, (gs.foldl step W).getD i false = if i < n+gs.length then t i else false := by
  induction gs generalizing W n with
  | nil => simpa using read
  | cons g gs ih =>
    obtain ⟨head,tail⟩ := ok
    have value : g.op.eval (g.inputs.map fun i => W.getD i false) = t n := by
      simpa only [read] using head
    have next (i : ℕ) : (step W g).getD i false = if i < n+1 then t i else false := by
      unfold step
      rw [value]
      rcases Nat.lt_trichotomy i n with h|h|h
      · rw [List.getD_append _ _ _ _ (by omega),read,if_pos h,if_pos (by omega)]
      · subst i
        simp [← len]
      · rw [List.getD_eq_default _ _ (by simp [len];omega),if_neg (by omega)]
    have more := ih (n+1) (step W g) (by simp [step,len]) next tail
    simpa only [List.foldl_cons,List.length_cons,show n+1+gs.length=n+(gs.length+1) by omega] using more

def group0 : List Gate := [⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [14, 20]⟩, ⟨.and, [14, 21]⟩, ⟨.and, [16, 19]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [3, 19]⟩]
def group1 : List Gate := [⟨.and, [5, 15]⟩, ⟨.and, [15, 17]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [11, 18]⟩, ⟨.and, [0, 22]⟩, ⟨.and, [1, 23]⟩, ⟨.and, [2, 19]⟩, ⟨.and, [4, 15]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [8, 16]⟩]
def group2 : List Gate := [⟨.and, [12, 14]⟩, ⟨.and, [1, 22]⟩, ⟨.and, [6, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.and, [9, 16]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [0, 20]⟩, ⟨.and, [0, 23]⟩, ⟨.and, [1, 20]⟩, ⟨.and, [3, 9]⟩, ⟨.and, [4, 18]⟩, ⟨.and, [5, 6]⟩]
def group3 : List Gate := [⟨.and, [6, 22]⟩, ⟨.and, [10, 25]⟩, ⟨.and, [0, 14]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [12, 18]⟩, ⟨.and, [12, 25]⟩, ⟨.and, [15, 23]⟩, ⟨.and, [16, 28]⟩, ⟨.and, [17, 24]⟩, ⟨.and, [17, 46]⟩]
def group4 : List Gate := [⟨.and, [0, 26]⟩, ⟨.and, [1, 30]⟩, ⟨.and, [5, 38]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [6, 30]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [7, 28]⟩, ⟨.and, [8, 21]⟩, ⟨.and, [9, 21]⟩, ⟨.and, [11, 43]⟩, ⟨.and, [13, 27]⟩]
def group5 : List Gate := [⟨.and, [13, 47]⟩, ⟨.and, [14, 32]⟩, ⟨.and, [15, 18]⟩, ⟨.and, [17, 31]⟩, ⟨.and, [17, 47]⟩, ⟨.and, [18, 27]⟩, ⟨.and, [21, 24]⟩, ⟨.and, [21, 27]⟩, ⟨.and, [21, 33]⟩, ⟨.and, [21, 49]⟩, ⟨.and, [24, 36]⟩, ⟨.and, [24, 50]⟩]
def group6 : List Gate := [⟨.and, [25, 29]⟩, ⟨.and, [44, 80]⟩, ⟨.and, [0, 16]⟩, ⟨.and, [0, 31]⟩, ⟨.and, [1, 32]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [3, 21]⟩, ⟨.and, [3, 27]⟩, ⟨.and, [3, 34]⟩, ⟨.and, [4, 7]⟩, ⟨.and, [4, 16]⟩, ⟨.and, [5, 9]⟩]
def group7 : List Gate := [⟨.and, [5, 24]⟩, ⟨.and, [6, 27]⟩, ⟨.and, [6, 45]⟩, ⟨.and, [7, 22]⟩, ⟨.and, [7, 30]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [8, 18]⟩, ⟨.and, [8, 22]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [10, 21]⟩, ⟨.and, [10, 31]⟩, ⟨.and, [10, 57]⟩]
def group8 : List Gate := [⟨.and, [11, 13]⟩, ⟨.and, [11, 26]⟩, ⟨.and, [11, 29]⟩, ⟨.and, [11, 58]⟩, ⟨.and, [12, 22]⟩, ⟨.and, [12, 33]⟩, ⟨.and, [12, 42]⟩, ⟨.and, [12, 43]⟩, ⟨.and, [13, 17]⟩, ⟨.and, [13, 18]⟩, ⟨.and, [13, 52]⟩, ⟨.and, [14, 41]⟩]
def group9 : List Gate := [⟨.and, [15, 19]⟩, ⟨.and, [15, 24]⟩, ⟨.and, [15, 52]⟩, ⟨.and, [16, 20]⟩, ⟨.and, [16, 22]⟩, ⟨.and, [16, 56]⟩, ⟨.and, [17, 34]⟩, ⟨.and, [18, 30]⟩, ⟨.and, [19, 23]⟩, ⟨.and, [19, 50]⟩, ⟨.and, [20, 26]⟩, ⟨.and, [20, 36]⟩]
def group10 : List Gate := [⟨.and, [20, 70]⟩, ⟨.and, [21, 25]⟩, ⟨.and, [21, 41]⟩, ⟨.and, [21, 42]⟩, ⟨.and, [22, 72]⟩, ⟨.and, [22, 77]⟩, ⟨.and, [23, 97]⟩, ⟨.and, [23, 105]⟩, ⟨.and, [24, 28]⟩, ⟨.and, [24, 33]⟩, ⟨.and, [24, 56]⟩, ⟨.and, [25, 39]⟩]
def group11 : List Gate := [⟨.and, [25, 48]⟩, ⟨.and, [26, 33]⟩, ⟨.and, [26, 37]⟩, ⟨.and, [26, 39]⟩, ⟨.and, [26, 64]⟩, ⟨.and, [26, 67]⟩, ⟨.and, [26, 88]⟩, ⟨.and, [27, 31]⟩, ⟨.and, [27, 35]⟩, ⟨.and, [28, 38]⟩, ⟨.and, [28, 51]⟩, ⟨.and, [28, 104]⟩]
def group12 : List Gate := [⟨.and, [29, 32]⟩, ⟨.and, [29, 41]⟩, ⟨.and, [29, 45]⟩, ⟨.and, [29, 74]⟩, ⟨.and, [29, 100]⟩, ⟨.and, [30, 37]⟩, ⟨.and, [30, 77]⟩, ⟨.and, [31, 40]⟩, ⟨.and, [31, 45]⟩, ⟨.and, [32, 39]⟩, ⟨.and, [32, 53]⟩, ⟨.and, [32, 55]⟩]
def group13 : List Gate := [⟨.and, [33, 35]⟩, ⟨.and, [34, 37]⟩, ⟨.and, [34, 42]⟩, ⟨.and, [34, 86]⟩, ⟨.and, [34, 87]⟩, ⟨.and, [35, 41]⟩, ⟨.and, [35, 52]⟩, ⟨.and, [35, 54]⟩, ⟨.and, [35, 69]⟩, ⟨.and, [36, 42]⟩, ⟨.and, [36, 43]⟩, ⟨.and, [36, 51]⟩]
def group14 : List Gate := [⟨.and, [37, 39]⟩, ⟨.and, [37, 48]⟩, ⟨.and, [37, 94]⟩, ⟨.and, [38, 40]⟩, ⟨.and, [38, 51]⟩, ⟨.and, [38, 67]⟩, ⟨.and, [39, 60]⟩, ⟨.and, [39, 143]⟩, ⟨.and, [40, 86]⟩, ⟨.and, [40, 87]⟩, ⟨.and, [40, 92]⟩, ⟨.and, [41, 44]⟩]
def group15 : List Gate := [⟨.and, [42, 44]⟩, ⟨.and, [43, 44]⟩, ⟨.and, [45, 65]⟩, ⟨.and, [46, 50]⟩, ⟨.and, [48, 49]⟩, ⟨.and, [48, 51]⟩, ⟨.and, [49, 54]⟩, ⟨.and, [52, 95]⟩, ⟨.and, [53, 55]⟩, ⟨.and, [53, 177]⟩, ⟨.and, [54, 118]⟩, ⟨.and, [55, 66]⟩]
def group16 : List Gate := [⟨.and, [56, 106]⟩, ⟨.and, [57, 89]⟩, ⟨.and, [57, 186]⟩, ⟨.and, [58, 127]⟩, ⟨.and, [58, 167]⟩, ⟨.and, [59, 149]⟩, ⟨.and, [59, 159]⟩, ⟨.and, [59, 176]⟩, ⟨.and, [60, 138]⟩, ⟨.and, [60, 194]⟩, ⟨.and, [61, 137]⟩, ⟨.and, [61, 183]⟩]
def group17 : List Gate := [⟨.and, [61, 195]⟩, ⟨.and, [62, 112]⟩, ⟨.and, [62, 160]⟩, ⟨.and, [62, 184]⟩, ⟨.and, [63, 114]⟩, ⟨.and, [63, 121]⟩, ⟨.and, [64, 113]⟩, ⟨.and, [65, 172]⟩, ⟨.and, [66, 189]⟩, ⟨.and, [68, 90]⟩, ⟨.and, [68, 148]⟩, ⟨.and, [69, 144]⟩]
def group18 : List Gate := [⟨.and, [70, 196]⟩, ⟨.and, [71, 125]⟩, ⟨.and, [71, 182]⟩, ⟨.and, [72, 135]⟩, ⟨.and, [73, 136]⟩, ⟨.and, [73, 198]⟩, ⟨.and, [74, 200]⟩, ⟨.and, [75, 145]⟩, ⟨.and, [75, 147]⟩, ⟨.and, [76, 151]⟩, ⟨.and, [76, 181]⟩, ⟨.and, [78, 83]⟩]
def group19 : List Gate := [⟨.and, [78, 173]⟩, ⟨.and, [79, 152]⟩, ⟨.and, [79, 179]⟩, ⟨.and, [81, 91]⟩, ⟨.and, [81, 101]⟩, ⟨.and, [82, 133]⟩, ⟨.and, [82, 170]⟩, ⟨.and, [83, 128]⟩, ⟨.and, [84, 161]⟩, ⟨.and, [84, 178]⟩, ⟨.and, [85, 117]⟩, ⟨.and, [85, 122]⟩]
def group20 : List Gate := [⟨.and, [88, 109]⟩, ⟨.and, [93, 140]⟩, ⟨.and, [96, 203]⟩, ⟨.and, [98, 110]⟩, ⟨.and, [99, 169]⟩, ⟨.and, [102, 162]⟩, ⟨.and, [103, 171]⟩, ⟨.and, [107, 157]⟩, ⟨.and, [108, 156]⟩, ⟨.and, [111, 132]⟩, ⟨.and, [115, 155]⟩, ⟨.and, [116, 199]⟩]
def group21 : List Gate := [⟨.and, [119, 187]⟩, ⟨.and, [120, 197]⟩, ⟨.and, [123, 146]⟩, ⟨.and, [124, 164]⟩, ⟨.and, [126, 165]⟩, ⟨.and, [129, 206]⟩, ⟨.and, [130, 166]⟩, ⟨.and, [131, 180]⟩, ⟨.and, [134, 188]⟩, ⟨.and, [150, 201]⟩, ⟨.and, [154, 168]⟩, ⟨.or, [231, 228]⟩]
def group22 : List Gate := [⟨.or, [278, 235]⟩, ⟨.or, [279, 222]⟩, ⟨.or, [280, 192]⟩, ⟨.or, [281, 213]⟩, ⟨.or, [282, 212]⟩, ⟨.or, [283, 239]⟩, ⟨.or, [284, 266]⟩, ⟨.or, [285, 237]⟩, ⟨.or, [286, 234]⟩, ⟨.or, [287, 217]⟩, ⟨.or, [288, 227]⟩, ⟨.or, [289, 233]⟩]
def group23 : List Gate := [⟨.or, [290, 230]⟩, ⟨.or, [291, 238]⟩, ⟨.or, [292, 256]⟩, ⟨.or, [293, 245]⟩, ⟨.or, [294, 265]⟩, ⟨.or, [295, 261]⟩, ⟨.or, [296, 277]⟩, ⟨.or, [297, 248]⟩, ⟨.or, [298, 252]⟩, ⟨.or, [299, 218]⟩, ⟨.or, [300, 236]⟩, ⟨.or, [301, 241]⟩]
def group24 : List Gate := [⟨.or, [302, 255]⟩, ⟨.or, [303, 185]⟩, ⟨.or, [304, 229]⟩, ⟨.or, [305, 271]⟩, ⟨.or, [306, 139]⟩, ⟨.or, [307, 210]⟩, ⟨.or, [308, 163]⟩, ⟨.or, [309, 219]⟩, ⟨.or, [310, 226]⟩, ⟨.or, [311, 190]⟩, ⟨.or, [312, 270]⟩, ⟨.or, [313, 232]⟩]
def group25 : List Gate := [⟨.or, [314, 251]⟩, ⟨.or, [315, 202]⟩, ⟨.or, [316, 243]⟩, ⟨.or, [317, 240]⟩, ⟨.or, [318, 242]⟩, ⟨.or, [319, 244]⟩, ⟨.or, [320, 257]⟩, ⟨.or, [321, 209]⟩, ⟨.or, [322, 267]⟩, ⟨.or, [323, 253]⟩, ⟨.or, [324, 208]⟩, ⟨.or, [325, 263]⟩]
def group26 : List Gate := [⟨.or, [326, 272]⟩, ⟨.or, [327, 249]⟩, ⟨.or, [328, 276]⟩, ⟨.or, [329, 224]⟩, ⟨.or, [330, 211]⟩, ⟨.or, [331, 204]⟩, ⟨.or, [332, 214]⟩, ⟨.or, [333, 262]⟩, ⟨.or, [334, 215]⟩, ⟨.or, [335, 191]⟩, ⟨.or, [336, 158]⟩, ⟨.or, [337, 205]⟩]
def group27 : List Gate := [⟨.or, [338, 274]⟩, ⟨.or, [339, 254]⟩, ⟨.or, [340, 275]⟩, ⟨.or, [341, 268]⟩, ⟨.or, [342, 260]⟩, ⟨.or, [343, 207]⟩, ⟨.or, [344, 153]⟩, ⟨.or, [345, 141]⟩, ⟨.or, [346, 142]⟩, ⟨.or, [347, 273]⟩, ⟨.or, [348, 250]⟩, ⟨.or, [349, 264]⟩]
def group28 : List Gate := [⟨.or, [350, 259]⟩, ⟨.or, [351, 216]⟩, ⟨.or, [352, 246]⟩, ⟨.or, [353, 193]⟩, ⟨.or, [354, 247]⟩, ⟨.or, [355, 225]⟩, ⟨.or, [356, 258]⟩, ⟨.or, [357, 223]⟩, ⟨.or, [358, 174]⟩, ⟨.or, [359, 269]⟩, ⟨.or, [360, 220]⟩, ⟨.or, [361, 221]⟩]
def group29 : List Gate := [⟨.or, [362, 175]⟩, ⟨.not, [363]⟩]
def gs : List Gate := group0 ++ (group1 ++ (group2 ++ (group3 ++ (group4 ++ (group5 ++ (group6 ++ (group7 ++ (group8 ++ (group9 ++ (group10 ++ (group11 ++ (group12 ++ (group13 ++ (group14 ++ (group15 ++ (group16 ++ (group17 ++ (group18 ++ (group19 ++ (group20 ++ (group21 ++ (group22 ++ (group23 ++ (group24 ++ (group25 ++ (group26 ++ (group27 ++ (group28 ++ (group29 ++ ([]))))))))))))))))))))))))))))))
def C : Circuit := ⟨gs,364⟩
set_option maxRecDepth 250000 in
set_option maxHeartbeats 0 in
def good (g : Gate) : Bool := (match g.op with
  | .and | .or | .not => true
  | _ => false) && decide (g.inputs.length ≤ 2)
set_option maxRecDepth 10000 in
theorem fan : FanInTwo C := by
  have check : gs.all good = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp check g hg
  cases op : g.op <;> simp [good,op] at h ⊢ <;> exact h
set_option maxRecDepth 250000 in
set_option maxHeartbeats 0 in
theorem bound : C.size ≤ 374 := by decide +kernel

def tapeChunk0 (x : Fin 15 → Bool) := (#[x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, v15 x] : Array Bool)
def tapeChunk1 (x : Fin 15 → Bool) := (#[v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x, v30 x, v31 x] : Array Bool)
def tapeChunk2 (x : Fin 15 → Bool) := (#[v32 x, v33 x, v34 x, v35 x, v36 x, v37 x, v38 x, v39 x, v40 x, v41 x, v42 x, v43 x, v44 x, v45 x, v46 x, v47 x] : Array Bool)
def tapeChunk3 (x : Fin 15 → Bool) := (#[v48 x, v49 x, v50 x, v51 x, v52 x, v53 x, v54 x, v55 x, v56 x, v57 x, v58 x, v59 x, v60 x, v61 x, v62 x, v63 x] : Array Bool)
def tapeChunk4 (x : Fin 15 → Bool) := (#[v64 x, v65 x, v66 x, v67 x, v68 x, v69 x, v70 x, v71 x, v72 x, v73 x, v74 x, v75 x, v76 x, v77 x, v78 x, v79 x] : Array Bool)
def tapeChunk5 (x : Fin 15 → Bool) := (#[v80 x, v81 x, v82 x, v83 x, v84 x, v85 x, v86 x, v87 x, v88 x, v89 x, v90 x, v91 x, v92 x, v93 x, v94 x, v95 x] : Array Bool)
def tapeChunk6 (x : Fin 15 → Bool) := (#[v96 x, v97 x, v98 x, v99 x, v100 x, v101 x, v102 x, v103 x, v104 x, v105 x, v106 x, v107 x, v108 x, v109 x, v110 x, v111 x] : Array Bool)
def tapeChunk7 (x : Fin 15 → Bool) := (#[v112 x, v113 x, v114 x, v115 x, v116 x, v117 x, v118 x, v119 x, v120 x, v121 x, v122 x, v123 x, v124 x, v125 x, v126 x, v127 x] : Array Bool)
def tapeChunk8 (x : Fin 15 → Bool) := (#[v128 x, v129 x, v130 x, v131 x, v132 x, v133 x, v134 x, v135 x, v136 x, v137 x, v138 x, v139 x, v140 x, v141 x, v142 x, v143 x] : Array Bool)
def tapeChunk9 (x : Fin 15 → Bool) := (#[v144 x, v145 x, v146 x, v147 x, v148 x, v149 x, v150 x, v151 x, v152 x, v153 x, v154 x, v155 x, v156 x, v157 x, v158 x, v159 x] : Array Bool)
def tapeChunk10 (x : Fin 15 → Bool) := (#[v160 x, v161 x, v162 x, v163 x, v164 x, v165 x, v166 x, v167 x, v168 x, v169 x, v170 x, v171 x, v172 x, v173 x, v174 x, v175 x] : Array Bool)
def tapeChunk11 (x : Fin 15 → Bool) := (#[v176 x, v177 x, v178 x, v179 x, v180 x, v181 x, v182 x, v183 x, v184 x, v185 x, v186 x, v187 x, v188 x, v189 x, v190 x, v191 x] : Array Bool)
def tapeChunk12 (x : Fin 15 → Bool) := (#[v192 x, v193 x, v194 x, v195 x, v196 x, v197 x, v198 x, v199 x, v200 x, v201 x, v202 x, v203 x, v204 x, v205 x, v206 x, v207 x] : Array Bool)
def tapeChunk13 (x : Fin 15 → Bool) := (#[v208 x, v209 x, v210 x, v211 x, v212 x, v213 x, v214 x, v215 x, v216 x, v217 x, v218 x, v219 x, v220 x, v221 x, v222 x, v223 x] : Array Bool)
def tapeChunk14 (x : Fin 15 → Bool) := (#[v224 x, v225 x, v226 x, v227 x, v228 x, v229 x, v230 x, v231 x, v232 x, v233 x, v234 x, v235 x, v236 x, v237 x, v238 x, v239 x] : Array Bool)
def tapeChunk15 (x : Fin 15 → Bool) := (#[v240 x, v241 x, v242 x, v243 x, v244 x, v245 x, v246 x, v247 x, v248 x, v249 x, v250 x, v251 x, v252 x, v253 x, v254 x, v255 x] : Array Bool)
def tapeChunk16 (x : Fin 15 → Bool) := (#[v256 x, v257 x, v258 x, v259 x, v260 x, v261 x, v262 x, v263 x, v264 x, v265 x, v266 x, v267 x, v268 x, v269 x, v270 x, v271 x] : Array Bool)
def tapeChunk17 (x : Fin 15 → Bool) := (#[v272 x, v273 x, v274 x, v275 x, v276 x, v277 x, v278 x, v279 x, v280 x, v281 x, v282 x, v283 x, v284 x, v285 x, v286 x, v287 x] : Array Bool)
def tapeChunk18 (x : Fin 15 → Bool) := (#[v288 x, v289 x, v290 x, v291 x, v292 x, v293 x, v294 x, v295 x, v296 x, v297 x, v298 x, v299 x, v300 x, v301 x, v302 x, v303 x] : Array Bool)
def tapeChunk19 (x : Fin 15 → Bool) := (#[v304 x, v305 x, v306 x, v307 x, v308 x, v309 x, v310 x, v311 x, v312 x, v313 x, v314 x, v315 x, v316 x, v317 x, v318 x, v319 x] : Array Bool)
def tapeChunk20 (x : Fin 15 → Bool) := (#[v320 x, v321 x, v322 x, v323 x, v324 x, v325 x, v326 x, v327 x, v328 x, v329 x, v330 x, v331 x, v332 x, v333 x, v334 x, v335 x] : Array Bool)
def tapeChunk21 (x : Fin 15 → Bool) := (#[v336 x, v337 x, v338 x, v339 x, v340 x, v341 x, v342 x, v343 x, v344 x, v345 x, v346 x, v347 x, v348 x, v349 x, v350 x, v351 x] : Array Bool)
def tapeChunk22 (x : Fin 15 → Bool) := (#[v352 x, v353 x, v354 x, v355 x, v356 x, v357 x, v358 x, v359 x, v360 x, v361 x, v362 x, v363 x, v364 x] : Array Bool)
def tape (x : Fin 15 → Bool) (i : ℕ) : Bool :=
  let v := match i / 16 with
    | 0 => tapeChunk0 x
    | 1 => tapeChunk1 x
    | 2 => tapeChunk2 x
    | 3 => tapeChunk3 x
    | 4 => tapeChunk4 x
    | 5 => tapeChunk5 x
    | 6 => tapeChunk6 x
    | 7 => tapeChunk7 x
    | 8 => tapeChunk8 x
    | 9 => tapeChunk9 x
    | 10 => tapeChunk10 x
    | 11 => tapeChunk11 x
    | 12 => tapeChunk12 x
    | 13 => tapeChunk13 x
    | 14 => tapeChunk14 x
    | 15 => tapeChunk15 x
    | 16 => tapeChunk16 x
    | 17 => tapeChunk17 x
    | 18 => tapeChunk18 x
    | 19 => tapeChunk19 x
    | 20 => tapeChunk20 x
    | 21 => tapeChunk21 x
    | 22 => tapeChunk22 x
    | _ => #[]
  v[i % 16]?.getD false
theorem appendTrace (t : ℕ → Bool) (l r : List Gate) (n : ℕ) (hl : Trace t n l) (hr : Trace t (n+l.length) r) :
    Trace t n (l++r) := by
  induction l generalizing n with
  | nil => simpa using hr
  | cons g l ih =>
    obtain ⟨a,b⟩ := hl
    refine ⟨a,ih (n+1) b ?_⟩
    simpa only [List.length_cons,show n+1+l.length=n+(l.length+1) by omega] using hr
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace0 (x : Fin 15 → Bool) : Trace (tape x) 15 group0 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace1 (x : Fin 15 → Bool) : Trace (tape x) 27 group1 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace2 (x : Fin 15 → Bool) : Trace (tape x) 39 group2 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace3 (x : Fin 15 → Bool) : Trace (tape x) 51 group3 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace4 (x : Fin 15 → Bool) : Trace (tape x) 63 group4 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace5 (x : Fin 15 → Bool) : Trace (tape x) 75 group5 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace6 (x : Fin 15 → Bool) : Trace (tape x) 87 group6 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace7 (x : Fin 15 → Bool) : Trace (tape x) 99 group7 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace8 (x : Fin 15 → Bool) : Trace (tape x) 111 group8 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace9 (x : Fin 15 → Bool) : Trace (tape x) 123 group9 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace10 (x : Fin 15 → Bool) : Trace (tape x) 135 group10 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace11 (x : Fin 15 → Bool) : Trace (tape x) 147 group11 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace12 (x : Fin 15 → Bool) : Trace (tape x) 159 group12 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace13 (x : Fin 15 → Bool) : Trace (tape x) 171 group13 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace14 (x : Fin 15 → Bool) : Trace (tape x) 183 group14 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace15 (x : Fin 15 → Bool) : Trace (tape x) 195 group15 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace16 (x : Fin 15 → Bool) : Trace (tape x) 207 group16 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace17 (x : Fin 15 → Bool) : Trace (tape x) 219 group17 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace18 (x : Fin 15 → Bool) : Trace (tape x) 231 group18 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace19 (x : Fin 15 → Bool) : Trace (tape x) 243 group19 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace20 (x : Fin 15 → Bool) : Trace (tape x) 255 group20 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace21 (x : Fin 15 → Bool) : Trace (tape x) 267 group21 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace22 (x : Fin 15 → Bool) : Trace (tape x) 279 group22 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace23 (x : Fin 15 → Bool) : Trace (tape x) 291 group23 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace24 (x : Fin 15 → Bool) : Trace (tape x) 303 group24 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace25 (x : Fin 15 → Bool) : Trace (tape x) 315 group25 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace26 (x : Fin 15 → Bool) : Trace (tape x) 327 group26 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace27 (x : Fin 15 → Bool) : Trace (tape x) 339 group27 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace28 (x : Fin 15 → Bool) : Trace (tape x) 351 group28 := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
theorem goodTrace29 (x : Fin 15 → Bool) : Trace (tape x) 363 group29 := by exact ⟨rfl, rfl, True.intro⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem computation (x : Fin 15 → Bool) : C.eval (List.ofFn x) = v364 x := by
  have valid : Trace (tape x) 15 gs := by
    exact appendTrace _ group0 _ 15 (goodTrace0 x) (appendTrace _ group1 _ 27 (goodTrace1 x) (appendTrace _ group2 _ 39 (goodTrace2 x) (appendTrace _ group3 _ 51 (goodTrace3 x) (appendTrace _ group4 _ 63 (goodTrace4 x) (appendTrace _ group5 _ 75 (goodTrace5 x) (appendTrace _ group6 _ 87 (goodTrace6 x) (appendTrace _ group7 _ 99 (goodTrace7 x) (appendTrace _ group8 _ 111 (goodTrace8 x) (appendTrace _ group9 _ 123 (goodTrace9 x) (appendTrace _ group10 _ 135 (goodTrace10 x) (appendTrace _ group11 _ 147 (goodTrace11 x) (appendTrace _ group12 _ 159 (goodTrace12 x) (appendTrace _ group13 _ 171 (goodTrace13 x) (appendTrace _ group14 _ 183 (goodTrace14 x) (appendTrace _ group15 _ 195 (goodTrace15 x) (appendTrace _ group16 _ 207 (goodTrace16 x) (appendTrace _ group17 _ 219 (goodTrace17 x) (appendTrace _ group18 _ 231 (goodTrace18 x) (appendTrace _ group19 _ 243 (goodTrace19 x) (appendTrace _ group20 _ 255 (goodTrace20 x) (appendTrace _ group21 _ 267 (goodTrace21 x) (appendTrace _ group22 _ 279 (goodTrace22 x) (appendTrace _ group23 _ 291 (goodTrace23 x) (appendTrace _ group24 _ 303 (goodTrace24 x) (appendTrace _ group25 _ 315 (goodTrace25 x) (appendTrace _ group26 _ 327 (goodTrace26 x) (appendTrace _ group27 _ 339 (goodTrace27 x) (appendTrace _ group28 _ 351 (goodTrace28 x) (appendTrace _ group29 _ 363 (goodTrace29 x) (True.intro))))))))))))))))))))))))))))))
  have initial (j : Fin 15) : x j = tape x j.val := by fin_cases j <;> rfl
  have base (i : ℕ) : (List.ofFn x).getD i false = if i < 15 then tape x i else false := by
    by_cases h : i < 15
    · rw [if_pos h,List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn]
      exact initial ⟨i,h⟩
    · rw [if_neg h,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
  have result := trace_sound (tape x) gs 15 (List.ofFn x) List.length_ofFn base valid 364
  have small : 364 < 15 + gs.length := by decide +kernel
  rw [if_pos small] at result
  exact result

set_option maxRecDepth 30000 in
theorem term0 (x : Fin 15 → Bool) : v231 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) := by
  simp only [v231, v196, v70, v44, v43, v28, v17, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term1 (x : Fin 15 → Bool) : v228 x = (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) := by
  simp only [v228, v90, v68, v31, v30, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term2 (x : Fin 15 → Bool) : v235 x = (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) := by
  simp only [v235, v136, v73, v43, v25, v21, v18, v17, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term3 (x : Fin 15 → Bool) : v222 x = (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) := by
  simp only [v222, v184, v62, v48, v46, v37, v23, v21, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term4 (x : Fin 15 → Bool) : v192 x = (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) := by
  simp only [v192, v87, v40, v29, v25, v22, v20, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term5 (x : Fin 15 → Bool) : v213 x = (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v213, v159, v59, v32, v29, v23, v21, v18, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term6 (x : Fin 15 → Bool) : v212 x = (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) := by
  simp only [v212, v149, v59, v37, v26, v23, v21, v19, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term7 (x : Fin 15 → Bool) : v239 x = (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) := by
  simp only [v239, v147, v75, v48, v47, v25, v20, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term8 (x : Fin 15 → Bool) : v266 x = (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) := by
  simp only [v266, v199, v116, v49, v48, v33, v22, v20, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term9 (x : Fin 15 → Bool) : v237 x = (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) := by
  simp only [v237, v200, v74, v51, v48, v27, v22, v20, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term10 (x : Fin 15 → Bool) : v234 x = (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) := by
  simp only [v234, v135, v72, v70, v28, v21, v20, v17, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term11 (x : Fin 15 → Bool) : v217 x = (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) := by
  simp only [v217, v137, v61, v41, v24, v21, v19, v17, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term12 (x : Fin 15 → Bool) : v227 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) := by
  simp only [v227, v189, v66, v60, v39, v28, v17, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term13 (x : Fin 15 → Bool) : v233 x = (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v233, v182, v71, v51, v36, v22, v21, v20, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term14 (x : Fin 15 → Bool) : v230 x = (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) := by
  simp only [v230, v144, v69, v33, v24, v22, v20, v19, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term15 (x : Fin 15 → Bool) : v238 x = (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) := by
  simp only [v238, v145, v75, v56, v47, v24, v20, v19, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term16 (x : Fin 15 → Bool) : v256 x = (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v256, v140, v93, v77, v22, v21, v20, v18, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term17 (x : Fin 15 → Bool) : v245 x = (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) := by
  simp only [v245, v179, v79, v69, v47, v35, v20, v19, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term18 (x : Fin 15 → Bool) : v265 x = (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) := by
  simp only [v265, v155, v115, v35, v27, v22, v20, v19, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term19 (x : Fin 15 → Bool) : v261 x = (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) := by
  simp only [v261, v171, v103, v35, v33, v30, v22, v20, v19, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term20 (x : Fin 15 → Bool) : v277 x = (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) := by
  simp only [v277, v168, v154, v39, v32, v31, v27, v18, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term21 (x : Fin 15 → Bool) : v248 x = (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) := by
  simp only [v248, v133, v82, v27, v26, v21, v20, v19, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term22 (x : Fin 15 → Bool) : v252 x = (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) := by
  simp only [v252, v178, v84, v54, v49, v35, v21, v19, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term23 (x : Fin 15 → Bool) : v218 x = (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) := by
  simp only [v218, v183, v61, v39, v37, v24, v19, v17, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term24 (x : Fin 15 → Bool) : v236 x = (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v236, v198, v73, v50, v46, v43, v23, v21, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term25 (x : Fin 15 → Bool) : v241 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) := by
  simp only [v241, v181, v76, v43, v36, v32, v18, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term26 (x : Fin 15 → Bool) : v255 x = (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) := by
  simp only [v255, v109, v88, v80, v44, v31, v27, v18, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term27 (x : Fin 15 → Bool) : v185 x = (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) := by
  simp only [v185, v94, v37, v27, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term28 (x : Fin 15 → Bool) : v229 x = (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) := by
  simp only [v229, v148, v68, v33, v30, v26, v22, v20, v19, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term29 (x : Fin 15 → Bool) : v271 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) := by
  simp only [v271, v165, v126, v77, v30, v20, v18, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term30 (x : Fin 15 → Bool) : v139 x = (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v139, v72, v22, v21, v20, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term31 (x : Fin 15 → Bool) : v210 x = (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) := by
  simp only [v210, v127, v58, v25, v22, v20, v18, v17, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term32 (x : Fin 15 → Bool) : v163 x = (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) := by
  simp only [v163, v100, v29, v27, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term33 (x : Fin 15 → Bool) : v219 x = (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) := by
  simp only [v219, v195, v61, v44, v42, v24, v19, v17, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term34 (x : Fin 15 → Bool) : v226 x = (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) := by
  simp only [v226, v172, v65, v38, v37, v34, v23, v21, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term35 (x : Fin 15 → Bool) : v190 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) := by
  simp only [v190, v143, v39, v28, v24, v19, v17, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term36 (x : Fin 15 → Bool) : v270 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) := by
  simp only [v270, v164, v124, v37, v30, v24, v19, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term37 (x : Fin 15 → Bool) : v232 x = (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) := by
  simp only [v232, v125, v71, v52, v25, v21, v18, v17, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term38 (x : Fin 15 → Bool) : v251 x = (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) := by
  simp only [v251, v161, v84, v49, v45, v29, v21, v20, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term39 (x : Fin 15 → Bool) : v202 x = (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) := by
  simp only [v202, v95, v52, v34, v25, v23, v21, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term40 (x : Fin 15 → Bool) : v243 x = (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v243, v173, v78, v42, v34, v31, v23, v21, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term41 (x : Fin 15 → Bool) : v240 x = (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) := by
  simp only [v240, v151, v76, v64, v32, v30, v26, v19, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term42 (x : Fin 15 → Bool) : v242 x = (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v242, v83, v78, v33, v31, v22, v21, v20, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term43 (x : Fin 15 → Bool) : v244 x = (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) := by
  simp only [v244, v152, v79, v67, v47, v26, v20, v19, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term44 (x : Fin 15 → Bool) : v257 x = (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) := by
  simp only [v257, v203, v96, v55, v53, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term45 (x : Fin 15 → Bool) : v209 x = (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) := by
  simp only [v209, v186, v57, v40, v38, v22, v20, v18, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term46 (x : Fin 15 → Bool) : v267 x = (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) := by
  simp only [v267, v187, v119, v51, v38, v22, v20, v17, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term47 (x : Fin 15 → Bool) : v253 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) := by
  simp only [v253, v117, v85, v42, v36, v24, v19, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term48 (x : Fin 15 → Bool) : v208 x = (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) := by
  simp only [v208, v89, v57, v18, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term49 (x : Fin 15 → Bool) : v263 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) := by
  simp only [v263, v156, v108, v38, v28, v21, v17, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term50 (x : Fin 15 → Bool) : v272 x = (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v272, v206, v129, v66, v55, v34, v23, v21, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term51 (x : Fin 15 → Bool) : v249 x = (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) := by
  simp only [v249, v170, v82, v55, v32, v27, v21, v18, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term52 (x : Fin 15 → Bool) : v276 x = (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) := by
  simp only [v276, v201, v150, v54, v49, v39, v26, v19, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term53 (x : Fin 15 → Bool) : v224 x = (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) := by
  simp only [v224, v121, v63, v52, v26, v25, v19, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term54 (x : Fin 15 → Bool) : v211 x = (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) := by
  simp only [v211, v167, v58, v45, v31, v25, v20, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term55 (x : Fin 15 → Bool) : v204 x = (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) := by
  simp only [v204, v177, v53, v52, v35, v25, v19, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term56 (x : Fin 15 → Bool) : v214 x = (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) := by
  simp only [v214, v176, v59, v41, v35, v23, v21, v19, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term57 (x : Fin 15 → Bool) : v262 x = (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) := by
  simp only [v262, v157, v107, v51, v28, v22, v20, v17, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term58 (x : Fin 15 → Bool) : v215 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) := by
  simp only [v215, v138, v60, v42, v28, v21, v17, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term59 (x : Fin 15 → Bool) : v191 x = (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) := by
  simp only [v191, v86, v50, v40, v24, v22, v20, v19, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term60 (x : Fin 15 → Bool) : v158 x = (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) := by
  simp only [v158, v104, v28, v17, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term61 (x : Fin 15 → Bool) : v205 x = (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) := by
  simp only [v205, v118, v54, v43, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term62 (x : Fin 15 → Bool) : v274 x = (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v274, v180, v131, v42, v36, v23, v21, v19, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term63 (x : Fin 15 → Bool) : v254 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) := by
  simp only [v254, v122, v85, v41, v36, v24, v19, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term64 (x : Fin 15 → Bool) : v275 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) := by
  simp only [v275, v188, v134, v67, v38, v36, v20, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term65 (x : Fin 15 → Bool) : v268 x = (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) := by
  simp only [v268, v197, v120, v65, v45, v38, v20, v18, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term66 (x : Fin 15 → Bool) : v260 x = (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) := by
  simp only [v260, v162, v102, v74, v29, v27, v22, v20, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term67 (x : Fin 15 → Bool) : v207 x = (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) := by
  simp only [v207, v106, v56, v22, v20, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term68 (x : Fin 15 → Bool) : v153 x = (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) := by
  simp only [v153, v88, v80, v44, v27, v26, v19, v18, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term69 (x : Fin 15 → Bool) : v141 x = (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) := by
  simp only [v141, v97, v23, v21, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term70 (x : Fin 15 → Bool) : v142 x = (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) := by
  simp only [v142, v105, v23, v21, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term71 (x : Fin 15 → Bool) : v273 x = (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) := by
  simp only [v273, v166, v130, v40, v31, v30, v22, v20, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term72 (x : Fin 15 → Bool) : v250 x = (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v250, v128, v83, v56, v33, v22, v21, v20, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term73 (x : Fin 15 → Bool) : v264 x = (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) := by
  simp only [v264, v132, v111, v50, v19, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term74 (x : Fin 15 → Bool) : v259 x = (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) := by
  simp only [v259, v169, v99, v53, v32, v24, v19, v18, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term75 (x : Fin 15 → Bool) : v216 x = (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) := by
  simp only [v216, v194, v60, v44, v41, v28, v17, v16, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term76 (x : Fin 15 → Bool) : v246 x = (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) := by
  simp only [v246, v91, v81, v32, v24, v21, v19, v18, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term77 (x : Fin 15 → Bool) : v193 x = (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) := by
  simp only [v193, v92, v40, v22, v20, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term78 (x : Fin 15 → Bool) : v247 x = (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) := by
  simp only [v247, v101, v81, v45, v24, v21, v20, v19, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term79 (x : Fin 15 → Bool) : v225 x = (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) := by
  simp only [v225, v113, v64, v30, v29, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term80 (x : Fin 15 → Bool) : v258 x = (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) := by
  simp only [v258, v110, v98, v57, v18, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term81 (x : Fin 15 → Bool) : v223 x = (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) := by
  simp only [v223, v114, v63, v58, v26, v25, v19, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term82 (x : Fin 15 → Bool) : v174 x = (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) := by
  simp only [v174, v86, v50, v34, v24, v23, v21, v19, v16, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term83 (x : Fin 15 → Bool) : v269 x = (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) := by
  simp only [v269, v146, v123, v39, v25, v19, v18, v17, v15, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term84 (x : Fin 15 → Bool) : v220 x = (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) := by
  simp only [v220, v112, v62, v46, v26, v23, v21, v19, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term85 (x : Fin 15 → Bool) : v221 x = (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) := by
  simp only [v221, v160, v62, v46, v41, v29, v23, v21, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
theorem term86 (x : Fin 15 → Bool) : v175 x = (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14) := by
  simp only [v175, v87, v34, v29, v25, v23, v21, v18, v17, Bool.and_true]
  all_goals ac_rfl
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem ev (x : Fin 15 → Bool) : C.eval (List.ofFn x) = !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14)) := by
  rw [computation]
  simp only [v364, v363, v362, v361, v360, v359, v358, v357, v356, v355, v354, v353, v352, v351, v350, v349, v348, v347, v346, v345, v344, v343, v342, v341, v340, v339, v338, v337, v336, v335, v334, v333, v332, v331, v330, v329, v328, v327, v326, v325, v324, v323, v322, v321, v320, v319, v318, v317, v316, v315, v314, v313, v312, v311, v310, v309, v308, v307, v306, v305, v304, v303, v302, v301, v300, v299, v298, v297, v296, v295, v294, v293, v292, v291, v290, v289, v288, v287, v286, v285, v284, v283, v282, v281, v280, v279, v278, Bool.or_false, term0, term1, term2, term3, term4, term5, term6, term7, term8, term9, term10, term11, term12, term13, term14, term15, term16, term17, term18, term19, term20, term21, term22, term23, term24, term25, term26, term27, term28, term29, term30, term31, term32, term33, term34, term35, term36, term37, term38, term39, term40, term41, term42, term43, term44, term45, term46, term47, term48, term49, term50, term51, term52, term53, term54, term55, term56, term57, term58, term59, term60, term61, term62, term63, term64, term65, term66, term67, term68, term69, term70, term71, term72, term73, term74, term75, term76, term77, term78, term79, term80, term81, term82, term83, term84, term85, term86]
end PEqualNP.Outside.L_meta_17126
theorem PEqualNP.Outside.L_meta_17126 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))) 374 := ⟨PEqualNP.Outside.L_meta_17126.C, PEqualNP.Outside.L_meta_17126.fan, PEqualNP.Outside.L_meta_17126.bound, PEqualNP.Outside.L_meta_17126.ev⟩
