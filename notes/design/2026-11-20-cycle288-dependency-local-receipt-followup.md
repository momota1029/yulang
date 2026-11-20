# Next design choices: carry source provenance without inventing a raw install

Cycle 288 separates three propositions that might otherwise be conflated.

1. A checked current frame and the original source are enough for the
   opaque leaf in the actual row-bearing endpoint. Neither a generated
   occurrence's identity by itself nor a packet that satisfies all stored
   model equations is enough: `ForeignLeaf288` preserves both, marks the
   wrong child syntactically discharged, and has no evidence under its
   actual registry. This example is deliberately outside the source-reachable
   ledger family; the original rules do not produce it.
2. A static extra plan makes the old cache proof possible but changes
   enabledness, even with identical full Models and output projection.
   The old source cannot install the semantic leaf anew because it is
   already committed; the append is not an available raw step. Treating
   it as a silent implementation detail would lose an actual refresh edge.
3. A sound refresh can make a fresh source-only *whole snapshot* certificate
   impossible. The source still permits setting slot 2 to Top. On that
   assignment the child head, no nested searches, capture checks, and
   class effects still pass. Only the ambient snapshot's new mark fails.
   Exact support is type 0 and row 0 for the child's root observation,
   types 1 and 2 for the new parent mark. The minimal support of neither
   observation is the full model predicate. The tentative `Receipt` uses
   whole Models only when producing ordinary current V8 evidence, not when
   establishing the root/nested reads and local equations from source.

## Next choices, in recommended order

- **Delay a rule change.** Add a separately checked provenance receipt to
  the replacement/rebase representation or observer, not to the old
  `State.plans` array. Its key has to bind the registry, declaration,
  actual emitted child, owning effect and selected context/embedding.
  Never equate Known/readback eligibility with "output queue empty".
  For this case the resulting quotient needs a distinct eligibility phase;
  the proved three-state observer is exact only with its Family premise.
- **Transport receipts with local input support.** State a proof obligation
  over a source-derived *typed* read set (root and actual nested positions),
  and a negative test against whole-Models/self-supported proofs. Existing
  `GeneralRebaseNonleafTransport276` and `SourceHeadTransport288` transport
  already verified local facts and ordered evidence; they do not establish
  coverage of aliases, non-inert children, default/effect outputs, or new
  owners. If an actual child needs the parent output, do not permit the
  empty source slice or install a well-founded premise by assumption.
- **Check the other bridge independently.** Current closed `Expr` cannot
  encode the row-parameter nominal on every assignment, and the recursive
  inspector still defers direct row decomposition (cycle 287). This cycle
  proves the opaque leaf's typed row port is retained by refinement, not
  that a row-pattern branch can read a new independent ambient row. Test
  a typed row-aware source expression and an actual compile-to-child
  path separately. No parser or spec change follows from the receipt.

First future integration test: use the positive/negative registries with
the same root layout and one additional alias or a real child effect.
Demand exact current-frame and identity correspondence and explicit live
request checks. An unscoped/stale receipt must not supply a parent fact.
Then rerun 199–240 diagnostic regressions and the known cycle cases before
any wider claim. Only after coverage and update preservation can an
I-49/I-50 measure be justified for source-reachable states.
