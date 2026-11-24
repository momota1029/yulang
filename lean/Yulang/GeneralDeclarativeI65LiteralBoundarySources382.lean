import Yulang.GeneralDeclarativeI65CarryBoundary382
import Yulang.GeneralDeclarativeWitnessSourceEndpoint359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessOpenSpine359 (Path)
open GeneralDeclarativeWitnessSourceEndpoint359 (Witness Read)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeRelease360 (ExactRelease)
open GeneralDeclarativeWhere319 (Capture)

def authoredPrimitiveRows382 {s : State} (c : SourceBoundary382 s) (rows : List Equation)
    (actual : ∀ row ∈ rows, row ∈ c.ledger.authored) :
    PrimitiveReads382 c (rows.map PrimitiveKey382.ordinary) :=
  match rows with
  | [] => .nil
  | first::rest =>
    .cons (.authored first (actual first List.mem_cons_self))
      (authoredPrimitiveRows382 c rest (fun row present => actual row (List.mem_cons_of_mem _ present)))

theorem authored_primitive_rows_keep_direct_routes382
    {s : State} (c : SourceBoundary382 s) (rows : List Equation)
    (actual : ∀ row ∈ rows, row ∈ c.ledger.authored) :
    exactPrimitiveRoutes382 (authoredPrimitiveRows382 c rows actual) =
      List.replicate rows.length .authored := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
    simp only [authoredPrimitiveRows382,exactPrimitiveRoutes382,exactPrimitiveRoute382,
      List.length_cons,List.replicate_succ,ih]

def appendPrimitiveReads382 {s : State} {c : SourceBoundary382 s} {left right : List PrimitiveKey382}
    (first : PrimitiveReads382 c left) (last : PrimitiveReads382 c right) :
    PrimitiveReads382 c (left ++ right) :=
  match first with
  | .nil => last
  | .cons row rest => .cons row (appendPrimitiveReads382 rest last)

theorem append_primitive_reads_keeps_route_order382
    {s : State} {c : SourceBoundary382 s} {left right : List PrimitiveKey382}
    (first : PrimitiveReads382 c left) (last : PrimitiveReads382 c right) :
    exactPrimitiveRoutes382 (appendPrimitiveReads382 first last) =
      exactPrimitiveRoutes382 first ++ exactPrimitiveRoutes382 last := by
  induction first with
  | nil => rfl
  | cons row rest ih =>
    simp only [appendPrimitiveReads382,exactPrimitiveRoutes382,List.cons_append,ih]

/-- A genuine authored open spine yields the literal list of its
direct source rows. The author table must be the one retained at the
boundary, not another table chosen to make the read succeed. -/
def primitive_rows_of_authored_open_spine382
    {s : State} (c : SourceBoundary382 s) {source : Source} {root : Nat} {path : Path}
    (sameAuthor : source.authored = c.ledger.authored)
    (read : GeneralDeclarativeWitnessOpenSpine359.Read source s.current.ordinary root path) :
    PrimitiveReads382 c ((path.rows root).map PrimitiveKey382.ordinary) :=
  authoredPrimitiveRows382 c (path.rows root) (fun row present => sameAuthor ▸ read.authored row present)

def writtenEndpointRows382 (root : Nat) : Witness → List Equation
  | .literal expr => [⟨root,expr⟩]
  | .linked path => path.rows root

theorem actual_endpoint_has_literal_authored_rows382
    {s : State} (c : SourceBoundary382 s) {source : Source} {root : Nat} {w : Witness}
    (sameAuthor : source.authored = c.ledger.authored)
    (read : Read source s.current.ordinary root w) :
    ∃ rows : PrimitiveReads382 c ((writtenEndpointRows382 root w).map PrimitiveKey382.ordinary),
      exactPrimitiveRoutes382 rows = List.replicate (writtenEndpointRows382 root w).length .authored := by
  cases read with
  | literal original _ =>
    exact ⟨.cons (.authored _ (sameAuthor ▸ original)) .nil,rfl⟩
  | linked path =>
    exact ⟨primitive_rows_of_authored_open_spine382 c sameAuthor path,
      authored_primitive_rows_keep_direct_routes382 _ _ _⟩

/-- A truly mixed literal read sequence: lower authored projection,
upper authored projection, then an exact physically released write,
in one supplied boundary context. No center read, semantic equality,
candidate election, or grant generation occurs here. -/
theorem actual_two_endpoints_and_native_share_literal_source382
    {s : State} (c : SourceBoundary382 s) {source : Source} {span : Capture} {lo hi : Witness}
    (sameAuthor : source.authored = c.ledger.authored)
    (lower : Read source s.current.ordinary span.lower lo)
    (upper : Read source s.current.ordinary span.upper hi)
    {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s c.world written logical)
    (released : ExactRelease c.world.board c.gate written) :
    ∃ reads : PrimitiveReads382 c
        (((writtenEndpointRows382 span.lower lo).map PrimitiveKey382.ordinary ++
          (writtenEndpointRows382 span.upper hi).map PrimitiveKey382.ordinary) ++
          [.native written logical]),
      exactPrimitiveRoutes382 reads =
        (List.replicate (writtenEndpointRows382 span.lower lo).length .authored ++
          List.replicate (writtenEndpointRows382 span.upper hi).length .authored) ++ [.native] := by
  obtain ⟨first,a⟩ := actual_endpoint_has_literal_authored_rows382 c sameAuthor lower
  obtain ⟨last,b⟩ := actual_endpoint_has_literal_authored_rows382 c sameAuthor upper
  let pinned : BoundNativeRead381 s c.world c.gate written :=
    ⟨⟨c.world,rail.current,c.gate,written,released,rfl,rfl,rfl⟩,rfl,rfl⟩
  let native : PrimitiveReads382 c [.native written logical] :=
    .cons (.native written logical rail pinned) .nil
  refine ⟨appendPrimitiveReads382 (appendPrimitiveReads382 first last) native,?_⟩
  rw [append_primitive_reads_keeps_route_order382,append_primitive_reads_keeps_route_order382,a,b]
  rfl

/-- Exact failure of a mandatory observation under this supplied gate;
there is no claim about candidate rejection or alternative legal reads. -/
theorem ordered_primitive_reads_cannot_drop_native_gate382
    {s : State} (c : SourceBoundary382 s) {keys : List PrimitiveKey382}
    {written : Write} {logical : Nat} (needed : .native written logical ∈ keys)
    (absent : written.address ∉ c.gate.grants) :
    ¬Nonempty (PrimitiveReads382 c keys) :=
  fun reads => absent
    (((ordered_primitive_boundary_exact382 c keys).mp reads (.native written logical) needed).2)

end Yulang.GeneralDeclarativeI65
