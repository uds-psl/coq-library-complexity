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

printf "Problem definitions - non-flat & basic properties\n"
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
  theories/NP/L/GenNP.v\
  theories/NP/L/CanEnumTerm_def.v\
  theories/NP/L/LMGenNP.v


printf "Problem definitions - additional flat variants\n"
coqwc\
  theories/NP/SAT/CookLevin/Subproblems/FlatCC.v\
  theories/NP/SAT/CookLevin/Subproblems/FlatTCC.v

printf "NP-hardness of GenNP"
coqwc\
  theories/NP/L/GenNP_is_hard.v\
  theories/NP/L/CanEnumTerm.v\


printf "\n\nReductions\n\n"
printf "L to mTM\n"
coqwc\
  theories/NP/TM/L_to_LM.v\
  theories/NP/TM/LM_to_mTM.v\
  theories/NP/TM/M_LM2TM.v\

printf "mTM to TMGenNP\n"
coqwc\
  theories/NP/TM/M_multi2mono.v\
  theories/NP/TM/mTM_to_singleTapeTM.v\
  theories/TM/Single/EncodeTapesInvariants.v\
  theories/TM/Single/DecodeTape.v\
  theories/TM/Single/DecodeTapes.v


printf "TM to CC\n"
coqwc\
  theories/NP/SAT/CookLevin/Reductions/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.v\
  theories/NP/SAT/CookLevin/Reductions/PTCC_Preludes.v\
  theories/NP/SAT/CookLevin/Reductions/SingleTMGenNP_to_TCC.v\
  theories/NP/SAT/CookLevin/Reductions/FlatTCC_to_FlatCC.v\
  theories/NP/SAT/CookLevin/Reductions/TCC_to_CC.v\
  theories/NP/SAT/CookLevin/Reductions/FlatSingleTMGenNP_to_FlatTCC.v
printf "CC to SAT\n"
coqwc\
  theories/NP/SAT/CookLevin/Reductions/CC_homomorphisms.v\
  theories/NP/SAT/CookLevin/Reductions/CC_to_BinaryCC.v\
  theories/NP/SAT/CookLevin/Reductions/FlatCC_to_BinaryCC.v\
  theories/NP/SAT/CookLevin/Reductions/BinaryCC_to_FSAT.v\
  theories/NP/SAT/FSAT/FormulaEncoding.v\
  theories/NP/SAT/FSAT/FSAT_to_SAT.v

printf "SAT in NP\n"
coqwc theories/NP/SAT/SAT_inNP.v  


printf "External libraries (use +)\n"
coqwc\
  coq-library-undecidability/theories/L/L.v\
  coq-library-undecidability/theories/TM/TM.v\
  coq-library-undecidability/theories/TM/L/Alphabets.v\
  coq-library-undecidability/theories/TM/L/CaseCom.v\
  coq-library-undecidability/theories/TM/L/HeapInterpreter/LookupTM.v\
  coq-library-undecidability/theories/TM/L/HeapInterpreter/StepTM.v\
  coq-library-undecidability/theories/TM/L/HeapInterpreter/M_LHeapInterpreter.v\
  coq-library-undecidability/theories/TM/L/HeapInterpreter/UnfoldClos.v\
  coq-library-undecidability/theories/TM/L/HeapInterpreter/JumpTargetTM.v\
  coq-library-undecidability/theories/TM/L/Transcode/Boollist_to_Enc.v\
  coq-library-undecidability/theories/TM/L/Transcode/Enc_to_Boollist.v\
  coq-library-undecidability/theories/TM/L/Transcode/BoollistEnc.v\
  coq-library-undecidability/theories/TM/L/Eval.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/Compiler_spec.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/LComp_to_TMComp.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/Compiler_facts.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/Compiler_nat_facts.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/EncBoolsTM_boolList.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/Compiler.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/NaryApp.v\
  coq-library-undecidability/theories/TM/L/CompilerBoolFuns/ClosedLAdmissible.v\
  coq-library-undecidability/theories/TM/Util/Prelim.v\
  coq-library-undecidability/theories/TM/Util/Relations.v\
  coq-library-undecidability/theories/TM/Util/ArithPrelim.v\
  coq-library-undecidability/theories/TM/Util/VectorPrelim.v\
  coq-library-undecidability/theories/TM/Util/TM_facts.v\
  coq-library-undecidability/theories/TM/Basic/Basic.v\
  coq-library-undecidability/theories/TM/Basic/Null.v\
  coq-library-undecidability/theories/TM/Basic/Mono.v\
  coq-library-undecidability/theories/TM/Basic/Duo.v\
  coq-library-undecidability/theories/TM/Combinators/Combinators.v\
  coq-library-undecidability/theories/TM/Combinators/Switch.v\
  coq-library-undecidability/theories/TM/Combinators/SequentialComposition.v\
  coq-library-undecidability/theories/TM/Combinators/If.v\
  coq-library-undecidability/theories/TM/Combinators/While.v\
  coq-library-undecidability/theories/TM/Combinators/StateWhile.v\
  coq-library-undecidability/theories/TM/Combinators/Mirror.v\
  coq-library-undecidability/theories/TM/Lifting/Lifting.v\
  coq-library-undecidability/theories/TM/Lifting/LiftTapes.v\
  coq-library-undecidability/theories/TM/Lifting/LiftAlphabet.v\
  coq-library-undecidability/theories/TM/Compound/TMTac.v\
  coq-library-undecidability/theories/TM/Compound/Multi.v\
  coq-library-undecidability/theories/TM/Compound/WriteString.v\
  coq-library-undecidability/theories/TM/Compound/MoveToSymbol.v\
  coq-library-undecidability/theories/TM/Compound/CopySymbols.v\
  coq-library-undecidability/theories/TM/Compound/Shift.v\
  coq-library-undecidability/theories/TM/Compound/Compare.v\
  coq-library-undecidability/theories/TM/Code/Code.v\
  coq-library-undecidability/theories/TM/Code/CodeTM.v\
  coq-library-undecidability/theories/TM/Code/WriteValue.v\
  coq-library-undecidability/theories/TM/Code/ChangeAlphabet.v\
  coq-library-undecidability/theories/TM/Code/Copy.v\
  coq-library-undecidability/theories/TM/Code/CompareValue.v\
  coq-library-undecidability/theories/TM/Code/ProgrammingTools.v\
  coq-library-undecidability/theories/TM/Code/CaseNat.v\
  coq-library-undecidability/theories/TM/Code/CaseSum.v\
  coq-library-undecidability/theories/TM/Code/CaseList.v\
  coq-library-undecidability/theories/TM/Code/CaseFin.v\
  coq-library-undecidability/theories/TM/Code/CasePair.v\
  coq-library-undecidability/theories/TM/Code/CaseBool.v\
  coq-library-undecidability/theories/TM/Code/NatTM.v\
  coq-library-undecidability/theories/TM/Code/NatSub.v\
  coq-library-undecidability/theories/TM/Code/ListTM.v\
  coq-library-undecidability/theories/TM/Code/List/App.v\
  coq-library-undecidability/theories/TM/Code/List/Concat_Repeat.v\
  coq-library-undecidability/theories/TM/Code/List/Cons_constant.v\
  coq-library-undecidability/theories/TM/Code/List/Length.v\
  coq-library-undecidability/theories/TM/Code/List/Nth.v\
  coq-library-undecidability/theories/TM/Code/List/Rev.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/EncodeBinNumbers.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosDefinitions.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosPointers.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosHelperMachines.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosIncrementTM.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosCompareTM.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosShiftTM.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosAddTM.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/PosMultTM.v\
  coq-library-undecidability/theories/TM/Code/BinNumbers/NTM.v\
  coq-library-undecidability/theories/TM/Single/EncodeTapes.v\
  coq-library-undecidability/theories/TM/Single/StepTM.v\
  coq-library-undecidability/theories/TM/Univ/LookupAssociativeListTM.v\
  coq-library-undecidability/theories/TM/Univ/LowLevel.v\
  coq-library-undecidability/theories/TM/Univ/Univ.v\
  coq-library-undecidability/theories/TM/PrettyBounds/MaxList.v\
  coq-library-undecidability/theories/TM/PrettyBounds/SizeBounds.v\
  coq-library-undecidability/theories/TM/Hoare/Hoare.v\
  coq-library-undecidability/theories/TM/Hoare/HoareLogic.v\
  coq-library-undecidability/theories/TM/Hoare/HoareCombinators.v\
  coq-library-undecidability/theories/TM/Hoare/HoareRegister.v\
  coq-library-undecidability/theories/TM/Hoare/HoareTactics.v\
  coq-library-undecidability/theories/TM/Hoare/HoareTacticsView.v\
  coq-library-undecidability/theories/TM/Hoare/HoareExamples.v\
  coq-library-undecidability/theories/TM/Hoare/HoareMult.v\
  coq-library-undecidability/theories/TM/Hoare/HoareStdLib.v\
  coq-library-undecidability/theories/TM/Hoare/HoareLegacy.v\
  coq-library-undecidability/theories/L/Prelim/MoreBase.v\
  coq-library-undecidability/theories/L/Prelim/ARS.v\
  coq-library-undecidability/theories/L/Prelim/StringBase.v\
  coq-library-undecidability/theories/L/Prelim/MoreList.v\
  coq-library-undecidability/theories/L/Prelim/LoopSum.v\
  coq-library-undecidability/theories/L/Util/L_facts.v\
  coq-library-undecidability/theories/L/Tactics/Computable.v\
  coq-library-undecidability/theories/L/Tactics/ComputableTime.v\
  coq-library-undecidability/theories/L/Tactics/LTactics.v\
  coq-library-undecidability/theories/L/Tactics/Extract.v\
  coq-library-undecidability/theories/L/Tactics/GenEncode.v\
  coq-library-undecidability/theories/L/Tactics/Lbeta_nonrefl.v\
  coq-library-undecidability/theories/L/Tactics/Lproc.v\
  coq-library-undecidability/theories/L/Tactics/Lbeta.v\
  coq-library-undecidability/theories/L/Tactics/Reflection.v\
  coq-library-undecidability/theories/L/Tactics/LClos.v\
  coq-library-undecidability/theories/L/Tactics/LClos_Eval.v\
  coq-library-undecidability/theories/L/Tactics/Lrewrite.v\
  coq-library-undecidability/theories/L/Tactics/Lsimpl.v\
  coq-library-undecidability/theories/L/Tactics/ComputableTactics.v\
  coq-library-undecidability/theories/L/Tactics/ComputableDemo.v\
  coq-library-undecidability/theories/L/Tactics/mixedTactics.v\
  coq-library-undecidability/theories/L/Datatypes/LUnit.v\
  coq-library-undecidability/theories/L/Datatypes/LBool.v\
  coq-library-undecidability/theories/L/Datatypes/List/List_basics.v\
  coq-library-undecidability/theories/L/Datatypes/List/List_enc.v\
  coq-library-undecidability/theories/L/Datatypes/List/List_eqb.v\
  coq-library-undecidability/theories/L/Datatypes/List/List_extra.v\
  coq-library-undecidability/theories/L/Datatypes/List/List_fold.v\
  coq-library-undecidability/theories/L/Datatypes/List/List_in.v\
  coq-library-undecidability/theories/L/Datatypes/List/List_nat.v\
  coq-library-undecidability/theories/L/Datatypes/Lists.v\
  coq-library-undecidability/theories/L/Datatypes/LNat.v\
  coq-library-undecidability/theories/L/Datatypes/LOptions.v\
  coq-library-undecidability/theories/L/Datatypes/LProd.v\
  coq-library-undecidability/theories/L/Datatypes/LSum.v\
  coq-library-undecidability/theories/L/Datatypes/LTerm.v\
  coq-library-undecidability/theories/L/Datatypes/LFinType.v\
  coq-library-undecidability/theories/L/Datatypes/LVector.v\
  coq-library-undecidability/theories/L/Functions/EqBool.v\
  coq-library-undecidability/theories/L/Functions/Equality.v\
  coq-library-undecidability/theories/L/Functions/Encoding.v\
  coq-library-undecidability/theories/L/Functions/Decoding.v\
  coq-library-undecidability/theories/L/Functions/Proc.v\
  coq-library-undecidability/theories/L/Functions/Size.v\
  coq-library-undecidability/theories/L/Functions/Subst.v\
  coq-library-undecidability/theories/L/Functions/Eval.v\
  coq-library-undecidability/theories/L/Functions/LoopSum.v\
  coq-library-undecidability/theories/L/Functions/UnboundIteration.v\
  coq-library-undecidability/theories/L/Functions/FinTypeLookup.v\
  coq-library-undecidability/theories/L/Functions/EnumInt.v\
  coq-library-undecidability/theories/L/Functions/Ackermann.v\
  coq-library-undecidability/theories/L/TM/TMEncoding.v\
  coq-library-undecidability/theories/L/TM/TMinL.v\
  coq-library-undecidability/theories/L/TM/TMinL/TMinL_extract.v\
  coq-library-undecidability/theories/L/TM/TapeFuns.v\
  coq-library-undecidability/theories/L/Complexity/UpToC.v\
  coq-library-undecidability/theories/L/Complexity/UpToCNary.v\
  coq-library-undecidability/theories/L/Complexity/GenericNary.v\
  coq-library-undecidability/theories/L/Complexity/ResourceMeasures.v\
  coq-library-undecidability/theories/L/Complexity/LinDecode/LTD_def.v\
  coq-library-undecidability/theories/L/Complexity/LinDecode/LTDnat.v\
  coq-library-undecidability/theories/L/Complexity/LinDecode/LTDlist.v\
  coq-library-undecidability/theories/L/Complexity/LinDecode/LTDbool.v\
  coq-library-undecidability/theories/L/AbstractMachines/LargestVar.v\
  coq-library-undecidability/theories/L/AbstractMachines/FlatPro/Programs.v\
  coq-library-undecidability/theories/L/AbstractMachines/FlatPro/ProgramsDef.v\
  coq-library-undecidability/theories/L/AbstractMachines/FlatPro/LM_heap_def.v\
  coq-library-undecidability/theories/L/AbstractMachines/FlatPro/LM_heap_correct.v\
  coq-library-undecidability/theories/L/AbstractMachines/FlatPro/UnfoldClos.v\
  coq-library-undecidability/theories/L/Computability/Acceptability.v\
  coq-library-undecidability/theories/L/Computability/Computability.v\
  coq-library-undecidability/theories/L/Computability/Decidability.v\
  coq-library-undecidability/theories/L/Computability/Enum.v\
  coq-library-undecidability/theories/L/Computability/Fixpoints.v\
  coq-library-undecidability/theories/L/Computability/MuRec.v\
  coq-library-undecidability/theories/L/Computability/Partial.v\
  coq-library-undecidability/theories/L/Computability/Por.v\
  coq-library-undecidability/theories/L/Computability/Rice.v\
  coq-library-undecidability/theories/L/Computability/Scott.v\
  coq-library-undecidability/theories/L/Computability/Seval.v\
  coq-library-undecidability/theories/L/Computability/Synthetic.v\
  theories/L/AbstractMachines/TM_LHeapInterpreter/LMBounds.v\
  theories/L/AbstractMachines/TM_LHeapInterpreter/LMBounds_Loop.v\
  theories/L/AbstractMachines/AbstractSubstMachine.v\
  theories/L/AbstractMachines/AbstractHeapMachine.v\
  theories/L/AbstractMachines/AbstractHeapMachineDef.v\
  theories/L/AbstractMachines/UnfoldHeap.v\
  theories/L/AbstractMachines/FunctionalDefinitions.v\
  theories/L/AbstractMachines/LambdaDepth.v\
  theories/L/AbstractMachines/UnfoldTailRec.v\
  theories/L/AbstractMachines/FlatPro/Computable/Compile.v\
  theories/L/AbstractMachines/FlatPro/Computable/Decompile.v\
  theories/L/AbstractMachines/FlatPro/SizeAnalysisStep.v\
  theories/L/AbstractMachines/FlatPro/SizeAnalysisUnfoldClos.v\
  theories/L/AbstractMachines/FlatPro/Computable/LPro.v\
  theories/L/Datatypes/LDepPair.v

#Not relevant
#  theories/NP/L/GenNPBool.v\
#  theories/L/TM/TMflat.v\
#  theories/L/TM/CompCode.v\
#  theories/L/TM/TMunflatten.v\
#  theories/L/TM/TMflatEnc.v\
#  theories/L/TM/TMflatFun.v\
#  theories/L/TM/TMflatComp.v\
#  theories/L/TM/TapeDecode.v\
#  theories/L/TM/TMflatten.v
#  theories/TM/Code/Decode.v
#  theories/TM/Code/DecodeList.v
#  theories/TM/Code/DecodeBool.v