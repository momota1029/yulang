# Cycle250: snapshot RHSs for stable owner targets

Status: Draft implementation design; language semantics unchanged. I47(a).

249 accepts already-safe fresh blocks. This cycle constructs those blocks:
`refresh(old,raw) = dedup(transform(mapping old, raw))`. Targets remain literal;
all RHS expressions are evaluated through the old ordered substitution. If old
is safe and raw targets lie in old's domain, every transformed RHS is outside
that domain. Therefore the deduplicated list is safe without an extra acyclicity
premise about raw RHSs. Coherent duplicate source equations are retained exactly.

The intended judgement is TWO-STATE: new target value equals the raw RHS read
in the old snapshot. It is not the same as interpreting that raw RHS in the new
assignment. A regression must demonstrate this difference. No simultaneous
cyclic block is claimed solved. Concrete stable capture/merge expressions from
Definitions241 supply coherence. All target inclusion premises remain visible;
this does not yet cover a singleton-to-many new slot or a new owner.

The materialized frame update rewrites all metadata and consumers exactly as
249, installing this constructed safe block. Public models are preserved under
Formed and public privacy, with one witness for all fields. This reduces the
fresh-safe premise but does not prove source Step simulation, new metadata
correctness, unconditional EvidenceNode or Acc. Finite input lists are not a
termination measure. I45's point-descriptor restriction remains unchanged.
