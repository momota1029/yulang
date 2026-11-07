import Yulang.CommonNominalFullCarrier

/-! # Presence operations on the dedicated nominal carrier

The model exposes the same independent presence interface as old Common while
retaining nominal states inside every structural constructor. Construction,
cast and solver integration are stated in their own feature modules.
-/

namespace Yulang.CommonNominalFullCarrier

def pair (first last : Ty) : Ty := .pair (.node first) (.node last)
def arrow (arg : Ty) (argRow : Row) (result : Ty) (resultRow : Row) : Ty :=
  .arrow (.node arg) argRow (.node result) resultRow
def record (label : Nat) (payload rest : Ty) : Ty := .record label (.node payload) rest
def required (label : Nat) (payload : Ty) : Ty := record label payload .emptyRecord
def recordDefault (label : Nat) (source fallback : Ty) : Ty :=
  .recordDefault label source (.node fallback)
def variant (label : Nat) (payload : Ty) : Ty := .variant label (.node payload)

def model : Core.PresenceGeneration.Model where
  Ty := Ty
  Row := Row
  base := .base
  bottom := .bottom
  top := .top
  union := .union
  inter := .inter
  pair := pair
  emptyRecord := .emptyRecord
  exactEmpty := .exactEmpty
  required := required
  record := record
  recordDefault := recordDefault
  variant := variant
  arrow := arrow
  empty := Common.rowEmpty
  join := Common.rowJoin
  subTy := Subtype
  subRow := Common.rowLe

end Yulang.CommonNominalFullCarrier
