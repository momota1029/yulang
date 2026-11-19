import Yulang.GeneralNominalOriginCongruence238
import Yulang.GeneralNominalVersionedCycles232

namespace Yulang.GeneralRebaseOriginCongruence269
open GeneralNominalRecursiveInspection (Origin Test Observes)
open GeneralNominalOriginTerms (Same project arity same_symm same_trans)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Head Edge)
open CommonNominalFullCarrier

theorem equal_symm (h : Equal state a b) : Equal state b a :=
 fun model valid => same_symm (h model valid)

theorem equal_trans (aToB : Equal state a b) (bToC : Equal state b c) : Equal state a c :=
 fun model valid => same_trans (aToB model valid) (bToC model valid)

theorem self_left (equal : Equal state a b) : Equal state a a :=
 equal_trans equal (equal_symm equal)

theorem self_right (equal : Equal state a b) : Equal state b b :=
 equal_trans (equal_symm equal) equal

theorem head_transport (equal : Equal state a b) (head : Head state a test) : Head state b test := by
 intro model valid
 have same := equal model valid
 have old := head model valid
 refine ⟨same.2.1,?_⟩
 intro to seen
 obtain ⟨earlier,observed⟩ := same.1
 exact (GeneralNominalOriginCongruence238.test_iff (same.2.2 earlier to observed seen) test).mp (old.2 earlier observed)

theorem project_seen {model : GeneralNominalCommonBridge.Assignment} (same : Same model first last) (test : Test) (i : Fin (arity test))
 (seen : Observes model (project first test i) value) :
 Observes model (project last test i) value := by
 obtain ⟨other,observed⟩ := same.2.1
 cases test with
 | scalar => exact Fin.elim0 i
 | structural shape =>
   cases seen with
   | structural parent length equal found =>
     have meaning := same.2.2 _ _ parent observed
     exact .structural observed length ⟨subtype_trans meaning.2 equal.1,subtype_trans equal.2 meaning.1⟩ found
 | nominal name count =>
   cases seen with
   | nominal parent equal found =>
     have meaning := same.2.2 _ _ parent observed
     exact .nominal observed ⟨subtype_trans meaning.2 equal.1,subtype_trans equal.2 meaning.1⟩ found

theorem transport_project_left (equal : Equal state a b) (test : Test) (i : Fin (arity test))
 (matched : Equal state (project a test i) c) : Equal state (project b test i) c := by
 intro model valid
 have same := equal model valid
 have original := matched model valid
 obtain ⟨value,seen⟩ := original.1
 exact ⟨⟨value,project_seen same test i seen⟩,original.2.1,
   fun x y one two => original.2.2 x y (project_seen (same_symm same) test i one) two⟩

theorem edge_of_equiv (first : Equal state a a') (last : Equal state b b') (step : Edge state a b) :
 Edge state a' b' := by
 obtain ⟨parent,test,index,head,firstMatch,lastMatch⟩ := step
 exact ⟨parent,test,index,head,equal_trans (equal_symm first) firstMatch,equal_trans lastMatch last⟩

theorem edge_iff (first : Equal state a a') (last : Equal state b b') :
 Edge state a b ↔ Edge state a' b' :=
 ⟨edge_of_equiv first last,edge_of_equiv (equal_symm first) (equal_symm last)⟩

theorem edge_left_live (edge : Edge state a b) : Equal state a a := by
 obtain ⟨_,_,_,_,equal,_⟩ := edge
 exact self_left equal

theorem edge_right_live (edge : Edge state a b) : Equal state b b := by
 obtain ⟨_,_,_,_,_,equal⟩ := edge
 exact self_right equal

/-- The old existential parent does not create extra edges: the same test
and child may be read at the actual first origin, provided its all-model
definedness and self-agreement are retained. -/
theorem edge_normal (state : State roles) (first last : Origin) :
 Edge state first last ↔ Equal state first first ∧
 ∃ test, ∃ index : Fin (arity test), Head state first test ∧ Equal state (project first test index) last := by
 constructor
 · intro edge
   have live := edge_left_live edge
   obtain ⟨_,test,index,head,same,child⟩ := edge
   exact ⟨live,test,index,head_transport (equal_symm same) head,transport_project_left (equal_symm same) test index child⟩
 · rintro ⟨live,test,index,head,child⟩
   exact ⟨first,test,index,head,live,child⟩

end Yulang.GeneralRebaseOriginCongruence269
