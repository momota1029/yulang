import Yulang.GeneralSourceRoleCstNamingControl295

/-! A finite representation for the naming decisions consumed by one
declaration. Input order is retained; no output default is executed here. -/
namespace Yulang.GeneralSourceRoleCstNamingRequests295
open GeneralSourceRoleSpelling292 (Body Output Environment Role)
open GeneralSourceRoleLocalEnv292 (BodyAgree OutputAgree Agree)

inductive Query where
  | role (spelling : String)
  | output (role : Nat) (spelling : String)
  | constructor (spelling : String)
  deriving Repr, DecidableEq

def reply (e : Environment) : Query → Option Nat
  | .role n => e.role n
  | .output r n => e.output r n
  | .constructor n => e.nullaryConstructor n

def bodyQueries : Body → List Query
  | .nullary n => [.constructor n]
  | _ => []

def outputQueries (e : Environment) (r : Nat) (o : Output) : List Query :=
  .output r o.spelling ::
    (match e.output r o.spelling with
    | none => []
    | some _ => bodyQueries o.body)

def queryList (e : Environment) (r : Role) : List Query :=
  .role r.spelling ::
    (match e.role r.spelling with
      | none => []
      | some i => r.outputs.flatMap (outputQueries e i))

def SameReplies (e f : Environment) (qs : List Query) : Prop :=
  ∀ q ∈ qs, reply e q = reply f q

theorem same_replies_cons (e f : Environment) (x : Query) (xs : List Query) :
    SameReplies e f (x::xs) ↔ reply e x = reply f x ∧ SameReplies e f xs := by
  simp [SameReplies]

theorem query_body_exact (e f : Environment) (b : Body) :
    SameReplies e f (bodyQueries b) ↔ BodyAgree e f b := by
  cases b <;> simp [bodyQueries,BodyAgree,SameReplies,reply]

theorem query_output_exact (e f : Environment) (n : Nat) (o : Output) :
    SameReplies e f (outputQueries e n o) ↔ OutputAgree e f n o := by
  cases h : e.output n o.spelling with
  | none => simp [outputQueries,h,reply,OutputAgree,SameReplies]
  | some id =>
    rw [outputQueries,h,same_replies_cons,query_body_exact]
    simp [reply,OutputAgree,h]

theorem query_role_exact (e f : Environment) (r : Role) :
    SameReplies e f (queryList e r) ↔ Agree e f r := by
  cases h : e.role r.spelling with
  | none => simp [queryList,h,reply,Agree,SameReplies]
  | some id =>
    rw [queryList,h,same_replies_cons]
    simp only [Agree,h,reply,Option.some.injEq,forall_eq']
    refine and_congr_right fun _ => ?_
    constructor
    · intro all o m
      apply (query_output_exact ..).mp
      intro q here
      exact all q (List.mem_flatMap.mpr ⟨o,m,here⟩)
    · intro agree q got
      obtain ⟨o,belongs,here⟩ := List.mem_flatMap.mp got
      exact (query_output_exact ..).mpr (agree o belongs) q here

end Yulang.GeneralSourceRoleCstNamingRequests295
