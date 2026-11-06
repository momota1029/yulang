import Yulang.PresenceDataExamples

def main : IO Unit := do
  for (name, passed) in Yulang.PresenceDataExamples.checks do
    if passed then
      IO.println s!"PASS: {name}"
    else
      throw (IO.userError s!"FAIL: {name}")
