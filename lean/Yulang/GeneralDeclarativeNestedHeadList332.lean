import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeNestedMaterial332
import Yulang.GeneralDeclarativeInlineEndpoint331
import Yulang.GeneralDeclarativeOpaqueConserve328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedHeadList332
open GeneralDeclarations (Registry Declaration)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeNestedDecode332 (normalized normalized_sound)
open GeneralDeclarativeNestedMaterial332 (assemble assemble_exact computed_frame)
open GeneralDeclarativeGrowth327 (Extends fits trans)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeStableReads329 (Heads weakened)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open CommonRoleOutermostResolver (All₂)

/-- All argument reads share the same already-authorized source snapshot,
even while ordinary generated naming rows accumulate. No new generated
equation can certify itself, and repeated binders are kept as occurrences
until the later body compiler writes their explicit equality. -/
def captureArgs (src : Sources s) (c : Constructors) (i : Interpretation)
    (fixed : List Nat) (current : State) (xs : List Capture) (ps : List Pattern) :
    Option (State × List (Nat × Capture)) :=
  match xs,ps with
  | [],[] => some (current,[])
  | a::as,p::patterns => do
    let code ← translate c i (normalize p)
    let use ← normalized src c i .actual (.variable a.center) p
    let (next,spans) ← assemble current a fixed code use
    let (after,rest) ← captureArgs src c i fixed next as patterns
    pure (after,spans ++ rest)
  | _,_ => none


open GeneralDeclarativeObserverGrowth330 (sources_grow)
open GeneralDeclarativeInlineGrowth331 (extend)

/-- A successful executable scan yields the exact positional head-list proof
in the resulting state. Only the already authorized read index is consulted. -/
theorem capture_sound {s t : State} {p : Supported s done}
    (src : Sources (restriction p)) (old : Extends s t)
    (bounds : ∀ a ∈ xs, Bounds s a)
    (seen : captureArgs src c i fixed t xs ps = some (out,spans)) :
    Retains t out fixed ∧ Heads out c i xs ps spans ∧ ∀ o ∈ spans, Bounds out o.2 := by
  induction xs generalizing ps t out spans with
  | nil =>
    cases ps with
    | nil =>
      have same : (t,[]) = (out,spans) := Option.some.inj seen
      cases same
      exact ⟨GeneralDeclarativeOpaqueConserve328.refl _ _,.nil,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
    | cons b bs => cases seen
  | cons a as ih =>
    cases ps with
    | nil => cases seen
    | cons pat pats =>
      cases printed : translate c i (normalize pat) with
      | none => simp [captureArgs,printed] at seen
      | some code =>
        cases scanned : normalized src c i .actual (.variable a.center) pat with
        | none => simp [captureArgs,printed,scanned] at seen
        | some use =>
          cases made : assemble t a fixed code use with
          | none => simp [captureArgs,printed,scanned,made] at seen
          | some value =>
            rcases value with ⟨middle,current⟩
            cases next : captureArgs src c i fixed middle as pats with
            | none => simp [captureArgs,printed,scanned,made,next] at seen
            | some value =>
              rcases value with ⟨last,rest⟩
              have same : (last,current ++ rest) = (out,spans) := by
                simpa [captureArgs,printed,scanned,made,next] using seen
              cases same
              obtain ⟨rhs,same,read⟩ := normalized_sound scanned
              cases Option.some.inj (same.symm.trans printed)
              have atMid := computed_frame (fits old (bounds a List.mem_cons_self)) printed
                (extend (sources_grow p old) read) made
              obtain ⟨later,children,childBounds⟩ := ih (trans old atMid.1.grows)
                (fun arg present => bounds arg (List.mem_cons_of_mem _ present)) next
              refine ⟨GeneralDeclarativeOpaqueConserve328.chain atMid.1 later,
                .cons (by
                  obtain ⟨raw,body,pretty,entails,walk⟩ := atMid.2.1.actual
                  exact ⟨fits later.grows atMid.2.1.fits,raw,body,pretty,
                    GeneralDeclarativeGrowth327.derives later.grows entails,walk⟩) children,?_⟩
              intro whole bound
              rcases List.mem_append.mp bound with first|other
              · exact fits later.grows (atMid.2.2.2.1 whole first)
              · exact childBounds whole other


/-- Endpoint scanning is independent of both center allocations and chosen
output targets. None is only absence of this positive finite observation. -/
def probe (src : Sources s) (c : Constructors) (i : Interpretation) :
    List Capture → List Pattern → Bool
  | [],[] => true
  | a::as,p::ps =>
    (normalized src c i .lower (.variable a.lower) p).isSome &&
      (normalized src c i .upper (.variable a.upper) p).isSome && probe src c i as ps
  | _,_ => false

theorem probe_sound {s t : State} (src : Sources s)
    (bounds : ∀ a ∈ xs, Bounds t a) (hit : probe src c i xs ps = true) :
    All₂ (fun a p => Bounds t a ∧ ∃ code lo hi,
        translate c i (normalize p) = some code ∧
        GeneralDeclarativeInlineTrace331.Read s .lower (.variable a.lower) code lo ∧
        GeneralDeclarativeInlineTrace331.Read s .upper (.variable a.upper) code hi) xs ps := by
  induction xs generalizing ps with
  | nil =>
    cases ps with
    | nil => exact .nil
    | cons a as => cases hit
  | cons a as ih =>
    cases ps with
    | nil => cases hit
    | cons p ps =>
      simp only [probe,Bool.and_eq_true] at hit
      obtain ⟨lo,seenLo⟩ := Option.isSome_iff_exists.mp hit.1.1
      obtain ⟨hi,seenHi⟩ := Option.isSome_iff_exists.mp hit.1.2
      obtain ⟨code,pretty,atLo⟩ := normalized_sound seenLo
      obtain ⟨other,also,atHi⟩ := normalized_sound seenHi
      cases Option.some.inj (also.symm.trans pretty)
      exact .cons ⟨bounds a List.mem_cons_self,code,lo,hi,pretty,atLo,atHi⟩
        (ih (fun item prior => bounds item (List.mem_cons_of_mem _ prior)) hit.2)

theorem endpoint_list {s : State} (src : Sources s)
    (bounds : ∀ a ∈ xs, Bounds s a) (hit : probe src c i xs ps = true) :
    All₂ (Matches s c i) xs ps :=
  probe_sound src bounds hit

end Yulang.GeneralDeclarativeNestedHeadList332
