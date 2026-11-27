import Yulang.GeneralDeclarativeI65I74WrittenPattern460

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open Yulang.GeneralDeclarationPatterns (Pattern)

private def original : Pattern :=
  .record 7 (.join (.variant 8 (.app 99 [.var 1, .var 2]))
    (.variant 8 (.var 3))) (.record 7 (.var 4) (.var 5))

example : readTerm original =
    .record 7 (.join (.variant 8 (.app 99 (.cons (.var 1) (.cons (.var 2) .nil))))
      (.variant 8 (.var 3))) (.record 7 (.var 4) (.var 5)) := rfl

example : writeTerm (readTerm original) = original := write_read_term original

#print axioms write_read_term
#print axioms write_read_args
#print axioms read_write_term
#print axioms read_write_args
end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
