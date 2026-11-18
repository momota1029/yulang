import Yulang.GeneralRebaseRootTrace262
open Yulang
open GeneralFiniteAliasSearch262
example : connected [] 57 57 = true := by simp [connected, component, search, allVertices, rest, adjacent]
example : connected [] 57 58 = false := by simp [connected, component, search, allVertices, rest, adjacent]
example : connected [(1,1),(1,2),(1,2),(2,2),(7,8)] 1 2 = true := by simp [connected, component, search, allVertices, rest, frontier, adjacent]
example : connected [(1,1),(1,2),(1,2),(2,2),(7,8)] 2 1 = true := by simp [connected, component, search, allVertices, rest, frontier, adjacent]
example : connected [(1,1),(1,2),(1,2),(2,2),(7,8)] 1 8 = false := by simp [connected, component, search, allVertices, rest, frontier, adjacent]
example : connected [(1,1),(1,2),(1,2),(2,2),(7,8)] 100 100 = true := by simp [connected, component, search, allVertices, rest, adjacent]
example : connected [(4,99),(99,7)] 4 7 = true := by simp [connected, component, search, allVertices, rest, frontier, adjacent]
example : connected [(4,99),(99,7)] 4 100 = false := by simp [connected, component, search, allVertices, rest, frontier, adjacent]
example : component [(1,2),(1,2)] 1 = [1,2,2,1,1] := by simp [component, search, allVertices, rest, frontier, adjacent]
example : ([2,1,2,7,1].filter fun n => (component [(1,2)] 1).contains n) = [2,1,2,1] := by simp [component, search, allVertices, rest, frontier, adjacent]
#print axioms GeneralFiniteAliasClosure262.exact
#print axioms GeneralFiniteAliasSearch262.search_correct
#print axioms GeneralFiniteAliasSearch262.component_exact
#print axioms GeneralFiniteAliasSearch262.exact
#print axioms GeneralFiniteAliasSearch262.reference_eq
#print axioms GeneralRebaseExecutableRequests262.requests_eq
#print axioms GeneralRebaseRootTrace262.from_runs
#print axioms GeneralRebaseRootTrace262.to_runs
#print axioms GeneralRebaseRootTrace262.models_exact
#print axioms GeneralRebaseRootTrace262.certificate
