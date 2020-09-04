utlc : Type
pcf: Type
nat: Type

appUtlc : utlc -> utlc -> utlc
lamUtlc : (utlc -> utlc) -> utlc


constPcf : nat -> pcf
appPcf : pcf -> pcf -> pcf
lamPcf : (pcf -> pcf) -> pcf
fixPcf : pcf -> pcf
caseNatPcf : pcf -> pcf -> pcf -> pcf
succPcf : pcf
