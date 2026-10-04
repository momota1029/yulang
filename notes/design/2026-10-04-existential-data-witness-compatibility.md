# Existential data-witness compatibility

Status: Authoritative
Scope: future Yulang data-type/package representation and inference architecture
Approved-by: user (explicit direction in this conversation)
Approved-at: 2026-10-04
Drafted-by: primary
Reviewed-by: spec_auditor (scoped conformance review; no findings)
Supersedes: none

## User direction

The user states:

> Yulangでは将来的に存在型を導入して構わないものとして考えてください。特にデータ型について、内部 witness の型をすべて公開パラメータとして外へ持ち出す必要はなく、`exists 'a. ...` のように constructor / package 内へ隠せるとかなり簡潔になります。

This is a design premise, not a request to implement existentials in the
current inference machine or broaden current proof gates.

## Compatibility constraint

Future data-type and package representations may quantify over internal witness
types while exposing only the intended public parameters. In particular, an
architecture must not require every internal witness type to be reified as a
public data-type parameter merely because the current inference phase lacks
existential packaging.

When choosing a future representation or solver boundary, prefer one that can
add package-local existential binders and their scoped introduction/elimination
without redesigning the whole data-type carrier. This is an extensibility
constraint only; it does not select a carrier or require a specific mechanism.

## Explicit non-decisions and scope

This direction does not select **data existential** surface syntax, constructor
declaration rules, elimination typing, variance or subtyping behavior,
generalization rules, runtime representation, or implementation phase. It
does not require existential support in the current inference implementation,
add a premise to current proofs, or authorize broadening their source
fragments. The existing existential operation/request typing decisions remain
governed by their own source designs and are not reinterpreted here.

The quoted `exists 'a. ...` is illustrative notation only. This document records
future compatibility and must not be used as evidence that current data types
already support existential packaging.
