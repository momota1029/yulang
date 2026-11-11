# Ordinary-state scalar registry bridge (cycle114)

Status: Draft. Scope: I-16 P1 and P2, then P3 if time remains.

The fields being reduced are B4Bridges.frontierLocal and evidenceNode.
General-source obligations remain twelve out of twelve. This module does not
repair the old B4 target or make a new language-semantic decision.

## Input and independent judgments

Use arbitrary finite lists of real Roles.Impl declarations whose sole receiver
is int or str and whose where list is empty. A source entry carries role,
declaration identity, and scalar, and the implementation is generated from it.
The ordinary input is an arbitrary finite State and a receiver slot. No caller
passes solver success, an assigned type, a selected candidate, or a dictionary.
The actual ordinary solver checks consistency; paired source atoms identify a
scalar; the existing RoleDictionaries elaborator supplies the actual plan.

The independent classification has four cases for this fragment: pending when
no supported paired scalar evidence exists, rejected when a known receiver has
no matching declaration, ambiguous when two distinct declarations match, and
selected when exactly one matching declaration exists, retaining its actual
identity and empty where list. An inconsistent ordinary state is returned as a
separate unavailable result, not called a new role-rejection reason. Unsupported
bool/unit or structural types remain outside the supported materialization
fragment; pending here means no supported evidence, not a complete language
classification. K2 is not triggered by the finite nullary scalar heads.

## Required theorems

For every list of source entries, role, slot, ordinary state, and output,
execution succeeds with that classification iff the state has a Common model
and the independent classification holds. In particular, unknown receivers are
not inferred from a unique visible impl, and known empty registries reject.

For every selected output and every Common assignment satisfying the input
ordinary atoms, the selected source declaration is visible, has the required
role, and its scalar head is equivalent to the actual receiver value. Dictionary
identity and all children (the empty list here) are part of the statement.

Changing list order or multiplicity while preserving the visible declaration
set must preserve the returned classification and exact dictionary plan. This
is only visible-set invariance; it does not solve general where-child ordering.
