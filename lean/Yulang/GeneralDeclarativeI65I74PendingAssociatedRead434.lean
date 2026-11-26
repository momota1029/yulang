import Yulang.GeneralDeclarativeI65I74PendingAssociatedSource434
import Yulang.GeneralDeclarativeI65I74StructuralWhereRootRead432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65 WhereAssociated432
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open Checker408 (Problem)
open GeneralDeclarativeWhere319 (Capture)

private def captureKey434 (a : Capture) : Nat × Nat × Nat :=
  (a.lower,a.center,a.upper)

private theorem sameCaptureKey434 (a b : Capture) :
    captureKey434 a = captureKey434 b ↔ a = b := by
  cases a
  cases b
  simp [captureKey434]

local instance : DecidableEq Capture :=
  fun a b => decidable_of_iff (captureKey434 a = captureKey434 b) (sameCaptureKey434 a b)

private def outputKey434 (o : GeneralSourceState.Output) : Nat × Nat :=
  (o.name,o.target)

private theorem sameOutputKey434 (a b : GeneralSourceState.Output) :
    outputKey434 a = outputKey434 b ↔ a = b := by
  cases a
  cases b
  simp [outputKey434]

local instance : DecidableEq GeneralSourceState.Output :=
  fun a b => decidable_of_iff (outputKey434 a = outputKey434 b) (sameOutputKey434 a b)


structure Wire where
  parentEscape : ExactEscapeWire
  thisEscape : ExactEscapeWire
  separator : List Nat

structure EpisodeRead434 (p : Problem) where
  episode : LiteralEpisode434 p.state p.root
  rootSafe : ¬ RootCycle p.state p.root
  noReady : ∀ tag, ¬ GeneralDeclarativeLowerKnown321.Knows
    (GeneralDeclarativeOrigins321.restriction
      (GeneralDeclarativeWitnessOrigins350.support (actual_episode_attachment434 episode))) episode.a tag
  originalOutput : GeneralSourceState.Output
  output : p.root.demand.outputs = [originalOutput]
  atB : originalOutput.target = episode.b
  order : p.root.occurrence = episode.seed.issuer ++ [0]

/-- Read the original retained ordinary rows without removing any of
them. The authored observation list is read from the State; the wire
cannot omit another independent source or attest settlement. -/
def readLiteralEpisode434 (p : Problem) (w : Wire) : Option (EpisodeRead434 p) := do
  let c := p.state.core
  let raw := c.current.ordinary
  match seeds : c.origins, asked : p.root.demand.arguments, outAt : p.root.demand.outputs with
  | [seed],[arg],[out] =>
    match shape : seed.endpoint with
    | .nominal key [.inl (.point (.ordinary (.var a)))] =>
      if literal : arg = point a ∧ p.root.occurrence = seed.issuer ++ [0] then
        if names : seed.slot ≠ a ∧ seed.slot ≠ out.target ∧ a ≠ out.target then
          if rows : raw.equations =
              [outerRow434 key seed.slot a,retainedOutput434 key a out.target,untouchedOutput434 out.target] then
            if noExtra : (c.routes.isEmpty && c.current.visible.isEmpty &&
                raw.normal.ordinary.isEmpty && raw.normal.intervals.isEmpty) = true then
              let ⟨three,interval⟩ := splitAnd noExtra
              let ⟨two,atoms⟩ := splitAnd three
              let ⟨ar,native⟩ := splitAnd two
              if safe : checkExactEscape raw a w.thisEscape = true then
                let actual : LiteralEpisode434 p.state p.root :=
                  ⟨key,seed,a,out.target,shape,seeds,List.isEmpty_iff.mp ar,List.isEmpty_iff.mp native,
                    rows,List.isEmpty_iff.mp atoms,List.isEmpty_iff.mp interval,
                    names.1,names.2.1,names.2.2,asked.trans (congrArg (fun z => [z]) literal.1)⟩
                if noSupport : GeneralDeclarativeWitnessNoHead350.check raw
                    (episodeProvenance434 actual) a w.separator = true then
                  have noCycle : ¬ RootCycle p.state p.root := by
                    rintro ⟨member,inArgs,cyc⟩
                    rw [asked,literal.1] at inArgs
                    cases List.mem_singleton.mp inArgs
                    exact exact_escape_refutes_raw_root_K2410 safe cyc
                  pure ⟨actual,noCycle,GeneralDeclarativeWitnessNoHead350.unseen noSupport,
                    out,outAt,rfl,literal.2⟩
                else none
              else none
            else none
          else none
        else none
      else none
    | _ => none
  | _,_,_ => none

private theorem sameDemand434 {x y : GeneralDeclarativeDemand320.Demand}
    (role : x.role = y.role) (args : x.arguments = y.arguments) (out : x.outputs = y.outputs) : x = y := by
  cases x
  cases y
  simp_all

private theorem sameRequest434 {x y : Request}
    (site : x.occurrence = y.occurrence) (demand : x.demand = y.demand) : x = y := by
  cases x
  cases y
  simp_all

structure Replay434 (p : Problem) where
  original : OriginalPendingWhere434 p.state p.root
  rootSafe : ¬ RootCycle p.state p.root

/-- A finite literal-source read, not performed by candidate
expansion at the pending child. Only the parent independently
authored input is read; the child is recovered at its source order,
not given a new head and not recursively visited. -/
def replay434 (p : Problem) (w : Wire) : Option (Replay434 p) := do
  let input ← readLiteralEpisode434 p w
  let actual := input.episode
  let s := p.state
  let q := p.root
  let registry := authoredRegistry s.core.current
  match onlyDecl : registry.declarations with
  | [decl] =>
    match ownOut : decl.associated with
    | [outBody] =>
      let parent : Request := ⟨actual.seed.issuer,⟨q.demand.role,[point actual.seed.slot],
        [⟨outBody.name,actual.a⟩]⟩⟩
      let root ← readProvisionalWrapFrame432 ⟨s,parent⟩ ⟨0,0,2,w.parentEscape⟩
      let f := root.frame
      have fDecl : f.decl = decl := List.mem_singleton.mp (onlyDecl ▸ List.mem_of_getElem? f.authored)
      if sameCtor : root.ctor = actual.key then
        match bindAt : f.decl.outputBinders,whereAt : f.decl.requirements, childAt : frameWhereKids400 f with
        | [binder],[clause],[child] =>
          if literal : clause.arguments = [.var root.binder] ∧ clause.role = q.demand.role ∧
              outBody.rhs = .app actual.key [.var binder.name] ∧ input.originalOutput.name = outBody.name then
            if childSame : child.occurrence = q.occurrence ∧ child.demand.role = q.demand.role ∧
                child.demand.arguments = q.demand.arguments ∧ child.demand.outputs = q.demand.outputs then
              let eqChild := sameRequest434 childSame.1
                (sameDemand434 childSame.2.1 childSame.2.2.1 childSame.2.2.2)
              let i : Fin parent.demand.outputs.length := ⟨0,by change 0 < 1; decide⟩
              let result ← readOriginalOutput432 s f
                (root.declared.2 f.decl (List.mem_of_getElem? f.authored)) i 1
              if body : result.output.body = .explicit outBody then
                if coded : eqExpr result.code (.nominal actual.key [.variable actual.b]) = true then
                  let event : Event s parent :=
                    ⟨f,root.head,fun j => (show i = j from Fin.eq_of_val_eq (by
                      have h : j.val < 1 := j.isLt
                      change 0 = j.val
                      omega)) ▸ result.output⟩
                  have literalRow : fixedValueCode403 (event.outputs i).rhs =
                      some (.nominal actual.key [.variable actual.b]) :=
                    result.valueCode.trans (congrArg some ((eq_expr ..).mp coded))
                  have parentClause : event.kids = [q] := childAt.trans (congrArg (fun y => [y]) eqChild)
                  have assoc : event.frame.decl.associated = [outBody] := by
                    change f.decl.associated = [outBody]
                    rw [fDecl]
                    exact ownOut
                  have childOut : q.demand.outputs = [⟨outBody.name,actual.b⟩] :=
                    input.output.trans (congrArg (fun z => [z]) ((sameOutputKey434 ..).mp (by
                      simp [outputKey434,literal.2.2.2,input.atB,actual])))
                  let source : OriginalPendingWhere434 s q :=
                    ⟨actual,parent,rfl,rfl,rfl,event,root.declared,
                      onlyDecl.trans (congrArg (fun y => [y]) fDecl.symm),
                      root.binder,by simpa [sameCtor] using root.headLiteral,
                      binder,bindAt,clause,whereAt,literal.1,literal.2.1,parentClause,input.order,
                      i,rfl,outBody,assoc,childOut,body,literal.2.2.1,literalRow,input.noReady⟩
                  pure ⟨source,input.rootSafe⟩
                else none
              else none
            else none
          else none
        | _,_,_ => none
      else none
    | _ => none
  | _ => none

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
