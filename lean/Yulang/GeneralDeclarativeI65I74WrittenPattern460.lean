import Yulang.GeneralDeclarationPatterns

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open Yulang.GeneralDeclarationPatterns (Pattern)

mutual
  inductive Term where
    | var (name : Nat)
    | app (name : Nat) (args : Args)
    | record (label : Nat) (payload tail : Term)
    | variant (tag : Nat) (payload : Term)
    | join (left right : Term)
  inductive Args where
    | nil
    | cons (first : Term) (rest : Args)
end

mutual
  def readTerm : Pattern → Term
    | .var n => .var n
    | .app n ps => .app n (readArgs ps)
    | .record l p t => .record l (readTerm p) (readTerm t)
    | .variant t p => .variant t (readTerm p)
    | .join x y => .join (readTerm x) (readTerm y)
  def readArgs : List Pattern → Args
    | [] => .nil
    | p :: ps => .cons (readTerm p) (readArgs ps)
end

mutual
  def writeTerm : Term → Pattern
    | .var n => .var n
    | .app n ps => .app n (writeArgs ps)
    | .record l p t => .record l (writeTerm p) (writeTerm t)
    | .variant t p => .variant t (writeTerm p)
    | .join x y => .join (writeTerm x) (writeTerm y)
  def writeArgs : Args → List Pattern
    | .nil => []
    | .cons p ps => writeTerm p :: writeArgs ps
end

mutual
  @[simp] theorem write_read_term (p : Pattern) : writeTerm (readTerm p) = p := by
    cases p
    case var => rfl
    case app _ ps => simpa only [readTerm, writeTerm] using congrArg (Pattern.app _) (write_read_args ps)
    case record _ p t => simp only [readTerm, writeTerm, write_read_term p, write_read_term t]
    case variant _ p => simp only [readTerm, writeTerm, write_read_term p]
    case join x y => simp only [readTerm, writeTerm, write_read_term x, write_read_term y]
  @[simp] theorem write_read_args (ps : List Pattern) : writeArgs (readArgs ps) = ps := by
    cases ps
    case nil => rfl
    case cons p ps => simp only [readArgs, writeArgs, write_read_term p, write_read_args ps]
end

mutual
  @[simp] theorem read_write_term (p : Term) : readTerm (writeTerm p) = p := by
    cases p
    case var => rfl
    case app _ ps => simpa only [readTerm, writeTerm] using congrArg (Term.app _) (read_write_args ps)
    case record _ p t => simp only [readTerm, writeTerm, read_write_term p, read_write_term t]
    case variant _ p => simp only [readTerm, writeTerm, read_write_term p]
    case join x y => simp only [readTerm, writeTerm, read_write_term x, read_write_term y]
  @[simp] theorem read_write_args (ps : Args) : readArgs (writeArgs ps) = ps := by
    cases ps
    case nil => rfl
    case cons p ps => simp only [readArgs, writeArgs, read_write_term p, read_write_args ps]
end

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
