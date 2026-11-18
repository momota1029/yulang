import Yulang.GeneralDictionaryFastFill258
open Yulang
#eval ("public", GeneralDictionaryFastFill258.lower 0, GeneralDictionaryFastFill258.upper 4)
#eval ("first-lower", GeneralDictionaryFastFill258.lower (GeneralDictionaryLooseFamilyNames240.lower 1),
 GeneralDictionarySearchCost258.probes (fun i => GeneralDictionaryLooseFamilyNames240.lower (i+1))
 (GeneralDictionaryLooseFamilyNames240.lower 1) 0 (GeneralDictionaryLooseFamilyNames240.lower 1+1))
#eval ("first-upper", GeneralDictionaryFastFill258.upper (GeneralDictionaryLooseFamilyNames240.upper 0),
 GeneralDictionarySearchCost258.probes GeneralDictionaryLooseFamilyNames240.upper
 (GeneralDictionaryLooseFamilyNames240.upper 0) 0 (GeneralDictionaryLooseFamilyNames240.upper 0+1))
#eval ("actual-not-aggregate", GeneralDictionaryFastFill258.lower GeneralDictionaryLooseLoopPacket240.actual,
 GeneralDictionaryFastFill258.upper GeneralDictionaryLooseLoopPacket240.actual)
#eval ("actual-lower-probes", GeneralDictionarySearchCost258.probes (fun i => GeneralDictionaryLooseFamilyNames240.lower (i+1))
 GeneralDictionaryLooseLoopPacket240.actual 0 (GeneralDictionaryLooseLoopPacket240.actual+1))
#eval ("actual-upper-probes", GeneralDictionarySearchCost258.probes GeneralDictionaryLooseFamilyNames240.upper
 GeneralDictionaryLooseLoopPacket240.actual 0 (GeneralDictionaryLooseLoopPacket240.actual+1))
