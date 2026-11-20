import Yulang.GeneralRebaseRowFixtureDriver287

open Yulang.GeneralRebaseRowFixtureDriver287

#print axioms Yulang.GeneralRebaseRowFixtureDriver287.actually_read
#print axioms Yulang.GeneralRebaseRowFixtureDriver287.literal_result
#print axioms Yulang.GeneralRebaseRowFixtureDriver287.only_root_tree
#print axioms Yulang.GeneralRebaseRowFixtureDriver287.exact_run

#eval (run true).map Prod.snd
#eval (run false).map Prod.snd

#guard match run true with
  | some (_, .selected 0 [.selected 1 []]) => true
  | _ => false
#guard match run false with
  | some (_, .selected 0 [.pending]) => true
  | _ => false
