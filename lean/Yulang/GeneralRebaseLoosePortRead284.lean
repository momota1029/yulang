import Yulang.GeneralRebaseWindowPortSound284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLoosePortRead284
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseLoopSource240 (registry root snapshot)
open GeneralRebaseLooseMicro278 (raw)
open GeneralRebaseLoosePrivate278 (refreshed_exact reobserved_exact)
open GeneralRebaseLooseAliases283 (canonical)
open GeneralRebaseLoopBase282.Loose (decode_reach)
open GeneralRebaseLooseWindow284 (exact_unbounded_future Observe)
open GeneralRebaseWindowPortSound284 (equation)
open GeneralRebaseEpochWindow284 (view)
open GeneralRebaseWindowPorts284 (Port End Age rawAddr rawIndex rootName read present exact_reads previous_has_index)
open GeneralRebaseInstallTimeline278 (installedCount)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseWindowPaths284 (roundFuture compactFuture)
open GeneralRebaseWholeRow282 (Keeps initialNames)
open GeneralRebasePrivateStore282 (Joint)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonNominalFullCarrier (Equivalent)

theorem model_stage (t : Tick) (m : Assignment) :
    Models (raw t) m ↔ Models (state (installedCount t)) m := by
  rcases t with ⟨n,p⟩
  cases p
  · exact Iff.rfl
  · exact (refreshed_exact n m).symm.trans ((reobserved_exact n m).symm)
  · exact (reobserved_exact n m).symm

theorem correct (t : Tick) (port : Port) (base : Assignment) (good : Models (raw t) base)
    (addr : Nat) (available : read 4 (view t) port = some addr) :
    Equivalent (base (rawAddr lower upper t port)).1 (base addr).1 := by
  obtain ⟨available,eq⟩ := (exact_reads 4 t port addr).mp available
  have less := previous_has_index t port.age available
  have valid := (model_stage t base).mp good
  obtain ⟨memo,_,lowerRead,upperRead,all⟩ := canonical (installedCount t)
  rcases port with ⟨age,side⟩
  cases side
  · exact equation (decode_reach _) base valid memo (all base) _ _ ((lowerRead _ (by omega)).trans eq.symm)
  · exact equation (decode_reach _) base valid memo (all base) _ _ ((upperRead _ less).trans eq.symm)

theorem one_witness_with_ports (initial : Tick) (external : Assignment) (data : Payload) :
    (∃ a, Keeps (initialNames 4) a external ∧
      ∀ n, let t := roundFuture initial n
        Joint (raw t) registry root data a ∧ ∀ p k,
          read 4 (compactFuture (view initial) n) p = some k →
            Equivalent (a (rawAddr lower upper t p)).1 (external k).1) ↔
    Observe (view initial) external data := by
  constructor
  · rintro ⟨a,keeps,support⟩
    exact (exact_unbounded_future initial external data).mp ⟨a,keeps,fun n => (support n).1⟩
  · intro truth
    obtain ⟨a,keeps,all⟩ := (exact_unbounded_future initial external data).mpr truth
    refine ⟨a,keeps,fun n => ⟨all n,?_⟩⟩
    intro p k probe
    rw [GeneralRebaseWindowPaths284.every_future] at probe
    have eligible := GeneralRebaseWindowPorts284.root_bound 4 _ p k probe
    have visible : k ∈ initialNames 4 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at eligible
      rcases eligible with rfl|rfl <;> decide
    have eq := congrArg Prod.fst (keeps.1 k visible)
    rw [← eq]
    exact correct _ p a (all n).1 k probe

end Yulang.GeneralRebaseLoosePortRead284
