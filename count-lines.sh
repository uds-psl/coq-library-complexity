#!/bin/bash

printf "Basic complexity\n"
coqwc\
  theories/Complexity/Definitions.v\
  theories/Complexity/EncodableP.v\
  theories/Complexity/LinTimeDecodable.v\
  theories/Complexity/Monotonic.v\
  theories/Complexity/NP.v\
  theories/Complexity/ONotation.v\
  theories/Complexity/PolyTimeComputable.v\
  theories/Complexity/Subtypes.v

printf "Problem definitions - non-flat\n"
coqwc \
  theories/NP/SAT/SharedSAT.v\
  theories/NP/SAT/SAT.v\
  theories/NP/SAT/kSAT.v\
  theories/NP/SAT/FSAT/FSAT.v\
  theories/NP/SAT/CookLevin/Subproblems/BinaryCC.v\
  theories/NP/SAT/CookLevin/Subproblems/CC.v\
  theories/NP/SAT/CookLevin/Subproblems/TM_single.v\
  theories/NP/SAT/CookLevin/Subproblems/SingleTMGenNP.v\
  theories/NP/TM/TMGenNP_fixed_mTM.v\
  theories/NP/TM/TMGenNP.v\
  theories/NP/L/GenNP.v\
  theories/NP/L/GenNPBool.v\
  theories/NP/L/CanEnumTerm.v\
  theories/NP/L/GenNP_is_hard.v\
  theories/NP/L/LMGenNP.v


printf "Problem definitions - additional flat variants\n"
# note: we omit the flat variants of Turing machines already available in the library of undecidable problems
coqwc\
  theories/NP/SAT/CookLevin/Subproblems/FlatCC.v\
  theories/NP/SAT/CookLevin/Subproblems/FlatTCC.v

printf "\n\nReductions\n\n"
printf "L to LM\n"
coqwc\
  theories/NP/TM/L_to_LM.v

printf "LM to mTM\n"
coqwc\
  theories/NP/TM/LM_to_mTM.v\
  theories/NP/TM/M_LM2TM.v

printf "mTM to TMGenNP\n"
coqwc\
  theories/NP/TM/M_multi2mono.v\
  theories/NP/TM/mTM_to_singleTapeTM.v

printf "TM to CC\n"
coqwc\
  theories/NP/SAT/CookLevin/Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.v\
  theories/NP/SAT/CookLevin/Reductions/PTCC_Preludes.v\
  theories/NP/SAT/CookLevin/Reductions/SingleTMGenNP_to_TCC.v\
  theories/NP/SAT/CookLevin/Reductions/FlatTCC_to_FlatCC.v\
  theories/NP/SAT/CookLevin/Reductions/TCC_to_CC.v\
  theories/NP/SAT/CookLevin/Reductions/FlatSingleTMGenNP_to_FlatTCC.v
printf "CC to BCC\n"
coqwc\
  theories/NP/SAT/CookLevin/Reductions/CC_homomorphisms.v\
  theories/NP/SAT/CookLevin/Reductions/CC_to_BinaryCC.v\
  theories/NP/SAT/CookLevin/Reductions/FlatCC_to_BinaryCC.v
printf "BinaryCC to FSAT\n"
coqwc\
  theories/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.v\
  theories/NP/SAT/FSAT/FormulaEncoding.v
printf "FSAT to SAT\n"
coqwc\
  theories/NP/SAT/FSAT/FSAT_to_SAT.v



