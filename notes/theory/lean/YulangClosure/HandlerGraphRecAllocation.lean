import YulangClosure.HandlerGraphSafety
import YulangClosure.FiniteGuardDecision

/-! Candidate six-sort simultaneous recursive allocation. Source recursive names
are a local prefix; existing references remain actual old graph references.
No checker was run by this author. Production/native correspondence is open. -/
namespace YulangClosure.HandlerGraph.Recursive
open HigherOrder (Ty Context emptyContext extend ReceiptTemplate OperationInstance)
variable {R S T : Type} {xi : R → Ty} {nu : S → Ty} {tau : T → Ty}

mutual
  def closeNamesValue (f : R → T) (g : S → T) : Value R S → Value T Empty
    | .ref r => .ref (f r)
    | .recvar s => .ref (g s)
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (closeNamesComp f g m)
    | .inLeft v => .inLeft (closeNamesValue f g v)
    | .inRight v => .inRight (closeNamesValue f g v)
    | .both v => .both (closeNamesValue f g v)
    | .top v => .top (closeNamesValue f g v)
    | .view v o => .view (closeNamesValue f g v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (closeNamesComp f g body) (closeNamesAdapter f g consumer)
    | .wrap inner input output => .wrap (closeNamesValue f g inner) (closeNamesAdapter f g input) (closeNamesAdapter f g output)
  def closeNamesComp (f : R → T) (g : S → T) : Comp R S → Comp T Empty
    | .ret v => .ret (closeNamesValue f g v)
    | .force v => .force (closeNamesValue f g v)
    | .chooseLeft v => .chooseLeft (closeNamesValue f g v)
    | .chooseRight v => .chooseRight (closeNamesValue f g v)
    | .absurd v => .absurd (closeNamesValue f g v)
    | .bind m n => .bind (closeNamesComp f g m) (closeNamesComp f g n)
    | .unionCase v l right => .unionCase (closeNamesValue f g v) (closeNamesComp f g l) (closeNamesComp f g right)
    | .scope owner body => .scope owner (closeNamesComp f g body)
    | .expose ev rv body => .expose ev rv (closeNamesComp f g body)
    | .request op v k => .request op (closeNamesValue f g v) (closeNamesComp f g k)
    | .fail reason => .fail reason
    | .dynamicCall fn a => .dynamicCall (closeNamesValue f g fn) (closeNamesValue f g a)
    | .handle h m => .handle (closeNamesHandler f g h) (closeNamesComp f g m)
    | .tryValue h v arms => .tryValue (closeNamesHandler f g h) (closeNamesValue f g v) (closeNamesValueArms f g arms)
    | .waitValue h v arms attempt => .waitValue (closeNamesHandler f g h) (closeNamesValue f g v)
        (closeNamesValueArms f g arms) (closeNamesComp f g attempt)
    | .tryOperation h op p k arms => .tryOperation (closeNamesHandler f g h) op (closeNamesValue f g p)
        (closeNamesComp f g k) (closeNamesOperationArms f g arms)
    | .waitOperation h op p k arms attempt => .waitOperation (closeNamesHandler f g h) op (closeNamesValue f g p)
        (closeNamesComp f g k) (closeNamesOperationArms f g arms) (closeNamesComp f g attempt)
  def closeNamesHandler (f : R → T) (g : S → T) : Handler R S → Handler T Empty
    | .mk id a b vs os => .mk id a b (closeNamesValueArms f g vs) (closeNamesOperationArms f g os)
  def closeNamesValueArms (f : R → T) (g : S → T) : ValueArms R S → ValueArms T Empty
    | .nil => .nil
    | .cons body rest => .cons (closeNamesComp f g body) (closeNamesValueArms f g rest)
  def closeNamesOperationArms (f : R → T) (g : S → T) : OperationArms R S → OperationArms T Empty
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (closeNamesComp f g body)
        (closeNamesOperationArms f g rest)
  def closeNamesAdapter (f : R → T) (g : S → T) : Adapter R S → Adapter T Empty
    | .mk a b body paths views => .mk a b (closeNamesComp f g body) paths views
end

mutual
  theorem closeNamesValue_typed (h : ValueTyped xi nu env v a) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      ValueTyped tau emptyTy env (closeNamesValue f g v) a := by
    cases h with
    | ref r => simpa only [closeNamesValue, hf] using (ValueTyped.ref (xi := tau) (nu := emptyTy) (env := env) (f r))
    | recvar s => simpa only [closeNamesValue, hg] using (ValueTyped.ref (xi := tau) (nu := emptyTy) (env := env) (g s))
    | var h => exact .var h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (closeNamesComp_typed h f g hf hg)
    | inLeft h => exact .inLeft (closeNamesValue_typed h f g hf hg)
    | inRight h => exact .inRight (closeNamesValue_typed h f g hf hg)
    | top h => exact .top (closeNamesValue_typed h f g hf hg)
    | view h => exact .view (closeNamesValue_typed h f g hf hg)
    | both h k => exact .both (closeNamesValue_typed h f g hf hg) (closeNamesValue_typed k f g hf hg)
    | lambdaValue h k => exact .lambdaValue (closeNamesComp_typed h f g hf hg) (closeNamesAdapter_typed k f g hf hg)
    | lambdaComputation h k => exact .lambdaComputation (closeNamesComp_typed h f g hf hg) (closeNamesAdapter_typed k f g hf hg)
    | wrap h i o => exact .wrap (closeNamesValue_typed h f g hf hg) (closeNamesAdapter_typed i f g hf hg) (closeNamesAdapter_typed o f g hf hg)
  theorem closeNamesComp_typed (h : CompTyped xi nu env m a) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      CompTyped tau emptyTy env (closeNamesComp f g m) a := by
    cases h with
    | ret h => exact .ret (closeNamesValue_typed h f g hf hg)
    | force h => exact .force (closeNamesValue_typed h f g hf hg)
    | chooseLeft h => exact .chooseLeft (closeNamesValue_typed h f g hf hg)
    | chooseRight h => exact .chooseRight (closeNamesValue_typed h f g hf hg)
    | absurd h => exact .absurd (closeNamesValue_typed h f g hf hg)
    | bind h k => exact .bind (closeNamesComp_typed h f g hf hg) (closeNamesComp_typed k f g hf hg)
    | unionCase h l r =>
        exact .unionCase (closeNamesValue_typed h f g hf hg)
          (closeNamesComp_typed l f g hf hg) (closeNamesComp_typed r f g hf hg)
    | scope h => exact .scope (closeNamesComp_typed h f g hf hg)
    | expose h => exact .expose (closeNamesComp_typed h f g hf hg)
    | request h k => exact .request (closeNamesValue_typed h f g hf hg) (closeNamesComp_typed k f g hf hg)
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (closeNamesValue_typed h f g hf hg) (closeNamesValue_typed k f g hf hg)
    | handle hh hm => exact .handle (closeNamesHandler_typed hh f g hf hg) (closeNamesComp_typed hm f g hf hg)
    | tryValue hh hv hs => exact .tryValue (closeNamesHandler_typed hh f g hf hg) (closeNamesValue_typed hv f g hf hg) (closeNamesValueArms_typed hs f g hf hg)
    | waitValue hh hv hs hm => exact .waitValue (closeNamesHandler_typed hh f g hf hg) (closeNamesValue_typed hv f g hf hg) (closeNamesValueArms_typed hs f g hf hg) (closeNamesComp_typed hm f g hf hg)
    | tryOperation hh hp hk hs => exact .tryOperation (closeNamesHandler_typed hh f g hf hg) (closeNamesValue_typed hp f g hf hg) (closeNamesComp_typed hk f g hf hg) (closeNamesOperationArms_typed hs f g hf hg)
    | waitOperation hh hp hk hs hm => exact .waitOperation (closeNamesHandler_typed hh f g hf hg) (closeNamesValue_typed hp f g hf hg) (closeNamesComp_typed hk f g hf hg) (closeNamesOperationArms_typed hs f g hf hg) (closeNamesComp_typed hm f g hf hg)
  theorem closeNamesHandler_typed (h : HandlerTyped xi nu env handler a b) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      HandlerTyped tau emptyTy env (closeNamesHandler f g handler) a b := by
    cases h with
    | mk hv ho => exact .mk (closeNamesValueArms_typed hv f g hf hg) (closeNamesOperationArms_typed ho f g hf hg)
  theorem closeNamesValueArms_typed (h : ValueArmsTyped xi nu env arms a b) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      ValueArmsTyped tau emptyTy env (closeNamesValueArms f g arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (closeNamesComp_typed hb f g hf hg) (closeNamesValueArms_typed hr f g hf hg)
  theorem closeNamesOperationArms_typed (h : OperationArmsTyped xi nu env arms a b) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      OperationArmsTyped tau emptyTy env (closeNamesOperationArms f g arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (closeNamesComp_typed hb f g hf hg) (closeNamesOperationArms_typed hr f g hf hg)
  theorem closeNamesAdapter_typed (h : AdapterTyped xi nu env adapter a b) (f : R → T) (g : S → T)
      (hf : ∀ r, tau (f r) = xi r) (hg : ∀ s, tau (g s) = nu s) :
      AdapterTyped tau emptyTy env (closeNamesAdapter f g adapter) a b := by
    cases h with
    | mk h => exact .mk (closeNamesComp_typed h f g hf hg)
end


/-! Closure commutes with local operations on ALL six syntax sorts. -/
mutual
  theorem closeNamesValue_rename (v : Value R S) (f : R → T) (g : S → T)
      (r : Nat → Nat) :
      closeNamesValue f g (renameValue r v) = renameValue r (closeNamesValue f g v) := by
    cases v with
    | ref x => rfl
    | recvar x => rfl
    | var i => rfl
    | unit  => rfl
    | bool x => rfl
    | int x => rfl
    | floatBits x => rfl
    | string x => rfl
    | bytes x => rfl
    | path x => rfl
    | char x => rfl
    | delay m =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesComp_rename m f g r]
    | inLeft v =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesValue_rename v f g r]
    | inRight v =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesValue_rename v f g r]
    | both v =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesValue_rename v f g r]
    | top v =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesValue_rename v f g r]
    | view v o =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesValue_rename v f g r]
    | lambda mode receipt a b c body consumer =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesComp_rename body f g (Original.up r), closeNamesAdapter_rename consumer f g r]
    | wrap inner input output =>
        simp only [closeNamesValue, renameValue]
        rw [closeNamesValue_rename inner f g r, closeNamesAdapter_rename input f g r, closeNamesAdapter_rename output f g r]
  theorem closeNamesComp_rename (v : Comp R S) (f : R → T) (g : S → T)
      (r : Nat → Nat) :
      closeNamesComp f g (renameComp r v) = renameComp r (closeNamesComp f g v) := by
    cases v with
    | ret v =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename v f g r]
    | force v =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename v f g r]
    | chooseLeft v =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename v f g r]
    | chooseRight v =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename v f g r]
    | absurd v =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename v f g r]
    | bind m body =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesComp_rename m f g r, closeNamesComp_rename body f g (Original.up r)]
    | unionCase v l right =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename v f g r, closeNamesComp_rename l f g (Original.up r), closeNamesComp_rename right f g (Original.up r)]
    | scope owner body =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesComp_rename body f g r]
    | expose ev rv body =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesComp_rename body f g r]
    | request op v k =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename v f g r, closeNamesComp_rename k f g (Original.up r)]
    | fail reason => rfl
    | dynamicCall inner arg =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesValue_rename inner f g r, closeNamesValue_rename arg f g r]
    | handle h m =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesHandler_rename h f g r, closeNamesComp_rename m f g r]
    | tryValue h v arms =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesHandler_rename h f g r, closeNamesValue_rename v f g r, closeNamesValueArms_rename arms f g r]
    | waitValue h v arms attempt =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesHandler_rename h f g r, closeNamesValue_rename v f g r, closeNamesValueArms_rename arms f g r, closeNamesComp_rename attempt f g r]
    | tryOperation h op p k arms =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesHandler_rename h f g r, closeNamesValue_rename p f g r, closeNamesComp_rename k f g (Original.up r), closeNamesOperationArms_rename arms f g r]
    | waitOperation h op p k arms attempt =>
        simp only [closeNamesComp, renameComp]
        rw [closeNamesHandler_rename h f g r, closeNamesValue_rename p f g r, closeNamesComp_rename k f g (Original.up r), closeNamesOperationArms_rename arms f g r, closeNamesComp_rename attempt f g r]
  theorem closeNamesHandler_rename (v : Handler R S) (f : R → T) (g : S → T)
      (r : Nat → Nat) :
      closeNamesHandler f g (renameHandler r v) = renameHandler r (closeNamesHandler f g v) := by
    cases v with
    | mk identity a b vs os =>
        simp only [closeNamesHandler, renameHandler]
        rw [closeNamesValueArms_rename vs f g r, closeNamesOperationArms_rename os f g r]
  theorem closeNamesValueArms_rename (v : ValueArms R S) (f : R → T) (g : S → T)
      (r : Nat → Nat) :
      closeNamesValueArms f g (renameValueArms r v) = renameValueArms r (closeNamesValueArms f g v) := by
    cases v with
    | nil  => rfl
    | cons body rest =>
        simp only [closeNamesValueArms, renameValueArms]
        rw [closeNamesComp_rename body f g (Original.up r), closeNamesValueArms_rename rest f g r]
  theorem closeNamesOperationArms_rename (v : OperationArms R S) (f : R → T) (g : S → T)
      (r : Nat → Nat) :
      closeNamesOperationArms f g (renameOperationArms r v) = renameOperationArms r (closeNamesOperationArms f g v) := by
    cases v with
    | nil  => rfl
    | cons op eligible body rest =>
        simp only [closeNamesOperationArms, renameOperationArms]
        rw [closeNamesComp_rename body f g (Original.up (Original.up r)), closeNamesOperationArms_rename rest f g r]
  theorem closeNamesAdapter_rename (v : Adapter R S) (f : R → T) (g : S → T)
      (r : Nat → Nat) :
      closeNamesAdapter f g (renameAdapter r v) = renameAdapter r (closeNamesAdapter f g v) := by
    cases v with
    | mk a b body paths views =>
        simp only [closeNamesAdapter, renameAdapter]
        rw [closeNamesComp_rename body f g (Original.up r)]
end

theorem closeNames_lift (f : R → T) (g : S → T) (s : Nat → Value R S) :
    (fun i => closeNamesValue f g (lift s i)) = lift (fun i => closeNamesValue f g (s i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact closeNamesValue_rename (s i) f g Nat.succ

mutual
  theorem closeNamesValue_subst (v : Value R S) (f : R → T) (g : S → T)
      (s : Nat → Value R S) :
      closeNamesValue f g (substValue s v) =
        substValue (fun i => closeNamesValue f g (s i)) (closeNamesValue f g v) := by
    cases v with
    | ref x => rfl
    | recvar x => rfl
    | var i => rfl
    | unit  => rfl
    | bool x => rfl
    | int x => rfl
    | floatBits x => rfl
    | string x => rfl
    | bytes x => rfl
    | path x => rfl
    | char x => rfl
    | delay m =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesComp_subst m f g s]
    | inLeft v =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesValue_subst v f g s]
    | inRight v =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesValue_subst v f g s]
    | both v =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesValue_subst v f g s]
    | top v =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesValue_subst v f g s]
    | view v o =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesValue_subst v f g s]
    | lambda mode receipt a b c body consumer =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesComp_subst body f g (lift s), closeNamesAdapter_subst consumer f g s]
        simp only [closeNames_lift]
    | wrap inner input output =>
        simp only [closeNamesValue, substValue]
        rw [closeNamesValue_subst inner f g s, closeNamesAdapter_subst input f g s, closeNamesAdapter_subst output f g s]
  theorem closeNamesComp_subst (v : Comp R S) (f : R → T) (g : S → T)
      (s : Nat → Value R S) :
      closeNamesComp f g (substComp s v) =
        substComp (fun i => closeNamesValue f g (s i)) (closeNamesComp f g v) := by
    cases v with
    | ret v =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst v f g s]
    | force v =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst v f g s]
    | chooseLeft v =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst v f g s]
    | chooseRight v =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst v f g s]
    | absurd v =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst v f g s]
    | bind m body =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesComp_subst m f g s, closeNamesComp_subst body f g (lift s)]
        simp only [closeNames_lift]
    | unionCase v l right =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst v f g s, closeNamesComp_subst l f g (lift s), closeNamesComp_subst right f g (lift s)]
        simp only [closeNames_lift]
    | scope owner body =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesComp_subst body f g s]
    | expose ev rv body =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesComp_subst body f g s]
    | request op v k =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst v f g s, closeNamesComp_subst k f g (lift s)]
        simp only [closeNames_lift]
    | fail reason => rfl
    | dynamicCall inner arg =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesValue_subst inner f g s, closeNamesValue_subst arg f g s]
    | handle h m =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesHandler_subst h f g s, closeNamesComp_subst m f g s]
    | tryValue h v arms =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesHandler_subst h f g s, closeNamesValue_subst v f g s, closeNamesValueArms_subst arms f g s]
    | waitValue h v arms attempt =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesHandler_subst h f g s, closeNamesValue_subst v f g s, closeNamesValueArms_subst arms f g s, closeNamesComp_subst attempt f g s]
    | tryOperation h op p k arms =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesHandler_subst h f g s, closeNamesValue_subst p f g s, closeNamesComp_subst k f g (lift s), closeNamesOperationArms_subst arms f g s]
        simp only [closeNames_lift]
    | waitOperation h op p k arms attempt =>
        simp only [closeNamesComp, substComp]
        rw [closeNamesHandler_subst h f g s, closeNamesValue_subst p f g s, closeNamesComp_subst k f g (lift s), closeNamesOperationArms_subst arms f g s, closeNamesComp_subst attempt f g s]
        simp only [closeNames_lift]
  theorem closeNamesHandler_subst (v : Handler R S) (f : R → T) (g : S → T)
      (s : Nat → Value R S) :
      closeNamesHandler f g (substHandler s v) =
        substHandler (fun i => closeNamesValue f g (s i)) (closeNamesHandler f g v) := by
    cases v with
    | mk identity a b vs os =>
        simp only [closeNamesHandler, substHandler]
        rw [closeNamesValueArms_subst vs f g s, closeNamesOperationArms_subst os f g s]
  theorem closeNamesValueArms_subst (v : ValueArms R S) (f : R → T) (g : S → T)
      (s : Nat → Value R S) :
      closeNamesValueArms f g (substValueArms s v) =
        substValueArms (fun i => closeNamesValue f g (s i)) (closeNamesValueArms f g v) := by
    cases v with
    | nil  => rfl
    | cons body rest =>
        simp only [closeNamesValueArms, substValueArms]
        rw [closeNamesComp_subst body f g (lift s), closeNamesValueArms_subst rest f g s]
        simp only [closeNames_lift]
  theorem closeNamesOperationArms_subst (v : OperationArms R S) (f : R → T) (g : S → T)
      (s : Nat → Value R S) :
      closeNamesOperationArms f g (substOperationArms s v) =
        substOperationArms (fun i => closeNamesValue f g (s i)) (closeNamesOperationArms f g v) := by
    cases v with
    | nil  => rfl
    | cons op eligible body rest =>
        simp only [closeNamesOperationArms, substOperationArms]
        rw [closeNamesComp_subst body f g (lift (lift s)), closeNamesOperationArms_subst rest f g s]
        simp only [closeNames_lift]
  theorem closeNamesAdapter_subst (v : Adapter R S) (f : R → T) (g : S → T)
      (s : Nat → Value R S) :
      closeNamesAdapter f g (substAdapter s v) =
        substAdapter (fun i => closeNamesValue f g (s i)) (closeNamesAdapter f g v) := by
    cases v with
    | mk a b body paths views =>
        simp only [closeNamesAdapter, substAdapter]
        rw [closeNamesComp_subst body f g (lift s)]
        simp only [closeNames_lift]
end

mutual
  def injectValue : Value R Empty → Value R S
    | .ref r => .ref r
    | .recvar s => Empty.elim s
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (injectComp m)
    | .inLeft v => .inLeft (injectValue v)
    | .inRight v => .inRight (injectValue v)
    | .both v => .both (injectValue v)
    | .top v => .top (injectValue v)
    | .view v o => .view (injectValue v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (injectComp body) (injectAdapter consumer)
    | .wrap f input output => .wrap (injectValue f) (injectAdapter input) (injectAdapter output)
  def injectComp : Comp R Empty → Comp R S
    | .ret v => .ret (injectValue v)
    | .force v => .force (injectValue v)
    | .chooseLeft v => .chooseLeft (injectValue v)
    | .chooseRight v => .chooseRight (injectValue v)
    | .absurd v => .absurd (injectValue v)
    | .bind m n => .bind (injectComp m) (injectComp n)
    | .unionCase v l right => .unionCase (injectValue v) (injectComp l) (injectComp right)
    | .scope owner body => .scope owner (injectComp body)
    | .expose ev rv body => .expose ev rv (injectComp body)
    | .request op v k => .request op (injectValue v) (injectComp k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (injectValue f) (injectValue a)
    | .handle h m => .handle (injectHandler h) (injectComp m)
    | .tryValue h v arms => .tryValue (injectHandler h) (injectValue v) (injectValueArms arms)
    | .waitValue h v arms attempt => .waitValue (injectHandler h) (injectValue v)
        (injectValueArms arms) (injectComp attempt)
    | .tryOperation h op p k arms => .tryOperation (injectHandler h) op (injectValue p)
        (injectComp k) (injectOperationArms arms)
    | .waitOperation h op p k arms attempt => .waitOperation (injectHandler h) op (injectValue p)
        (injectComp k) (injectOperationArms arms) (injectComp attempt)
  def injectHandler : Handler R Empty → Handler R S
    | .mk id a b vs os => .mk id a b (injectValueArms vs) (injectOperationArms os)
  def injectValueArms : ValueArms R Empty → ValueArms R S
    | .nil => .nil
    | .cons body rest => .cons (injectComp body) (injectValueArms rest)
  def injectOperationArms : OperationArms R Empty → OperationArms R S
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (injectComp body)
        (injectOperationArms rest)
  def injectAdapter : Adapter R Empty → Adapter R S
    | .mk a b body paths views => .mk a b (injectComp body) paths views
end

mutual
  theorem injectValue_typed (h : ValueTyped xi emptyTy env v a)  :
      ValueTyped xi nu env (injectValue v) a := by
    cases h with
    | ref r => exact .ref r
    | recvar s => exact Empty.elim s
    | var h => exact .var h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (injectComp_typed h)
    | inLeft h => exact .inLeft (injectValue_typed h)
    | inRight h => exact .inRight (injectValue_typed h)
    | top h => exact .top (injectValue_typed h)
    | view h => exact .view (injectValue_typed h)
    | both h k => exact .both (injectValue_typed h) (injectValue_typed k)
    | lambdaValue h k => exact .lambdaValue (injectComp_typed h) (injectAdapter_typed k)
    | lambdaComputation h k => exact .lambdaComputation (injectComp_typed h) (injectAdapter_typed k)
    | wrap h i o => exact .wrap (injectValue_typed h) (injectAdapter_typed i) (injectAdapter_typed o)
  theorem injectComp_typed (h : CompTyped xi emptyTy env m a)  :
      CompTyped xi nu env (injectComp m) a := by
    cases h with
    | ret h => exact .ret (injectValue_typed h)
    | force h => exact .force (injectValue_typed h)
    | chooseLeft h => exact .chooseLeft (injectValue_typed h)
    | chooseRight h => exact .chooseRight (injectValue_typed h)
    | absurd h => exact .absurd (injectValue_typed h)
    | bind h k => exact .bind (injectComp_typed h) (injectComp_typed k)
    | unionCase h l r =>
        exact .unionCase (injectValue_typed h)
          (injectComp_typed l) (injectComp_typed r)
    | scope h => exact .scope (injectComp_typed h)
    | expose h => exact .expose (injectComp_typed h)
    | request h k => exact .request (injectValue_typed h) (injectComp_typed k)
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (injectValue_typed h) (injectValue_typed k)
    | handle hh hm => exact .handle (injectHandler_typed hh) (injectComp_typed hm)
    | tryValue hh hv hs => exact .tryValue (injectHandler_typed hh) (injectValue_typed hv) (injectValueArms_typed hs)
    | waitValue hh hv hs hm => exact .waitValue (injectHandler_typed hh) (injectValue_typed hv) (injectValueArms_typed hs) (injectComp_typed hm)
    | tryOperation hh hp hk hs => exact .tryOperation (injectHandler_typed hh) (injectValue_typed hp) (injectComp_typed hk) (injectOperationArms_typed hs)
    | waitOperation hh hp hk hs hm => exact .waitOperation (injectHandler_typed hh) (injectValue_typed hp) (injectComp_typed hk) (injectOperationArms_typed hs) (injectComp_typed hm)
  theorem injectHandler_typed (h : HandlerTyped xi emptyTy env handler a b)  :
      HandlerTyped xi nu env (injectHandler handler) a b := by
    cases h with
    | mk hv ho => exact .mk (injectValueArms_typed hv) (injectOperationArms_typed ho)
  theorem injectValueArms_typed (h : ValueArmsTyped xi emptyTy env arms a b)  :
      ValueArmsTyped xi nu env (injectValueArms arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (injectComp_typed hb) (injectValueArms_typed hr)
  theorem injectOperationArms_typed (h : OperationArmsTyped xi emptyTy env arms a b)  :
      OperationArmsTyped xi nu env (injectOperationArms arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (injectComp_typed hb) (injectOperationArms_typed hr)
  theorem injectAdapter_typed (h : AdapterTyped xi emptyTy env adapter a b)  :
      AdapterTyped xi nu env (injectAdapter adapter) a b := by
    cases h with
    | mk h => exact .mk (injectComp_typed h)
end

def joinTy (xi : R → Ty) (nu : S → Ty) : Sum R S → Ty
  | .inl r => xi r
  | .inr s => nu s

/-- Source convention: all n recursive names occupy the nearest prefix;
outer context index i occupies index n+i. Ordinary binders extend this context
one slot at a time. This is a concrete representation of Γ,x̄:Ā. -/
def sourceContext (nu : Fin n → Ty) (env : Context) : Context := fun i =>
  if h : i < n then some (nu ⟨i, h⟩) else env (i - n)

def splitNames (n : Nat) : Nat → Value R (Fin n) := fun i =>
  if h : i < n then .recvar ⟨i, h⟩ else .var (i - n)

theorem splitNames_typed {xi : R → Ty} {nu : Fin n → Ty} :
    SubstitutionTyped xi nu (sourceContext nu env) env (splitNames n) := by
  intro i a hi
  by_cases h : i < n
  · simp only [sourceContext, dite_eq_left h, Option.some.injEq] at hi
    subst a
    simpa only [splitNames, dite_eq_left h] using
      (ValueTyped.recvar (xi := xi) (nu := nu) (env := env) ⟨i, h⟩)
  · simp only [sourceContext, dite_eq_right h] at hi
    simpa only [splitNames, dite_eq_right h] using (ValueTyped.var (xi := xi) (nu := nu) hi)

def splitValue (n : Nat) (v : Value R Empty) : Value R (Fin n) :=
  substValue (splitNames n) (injectValue v)

def splitComp (n : Nat) (m : Comp R Empty) : Comp R (Fin n) :=
  substComp (splitNames n) (injectComp m)

def splitAdapter (n : Nat) (adapter : Adapter R Empty) : Adapter R (Fin n) :=
  substAdapter (splitNames n) (injectAdapter adapter)

theorem splitValue_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : ValueTyped xi emptyTy (sourceContext nu env) v a) :
    ValueTyped xi nu env (splitValue n v) a :=
  substValue_typed (injectValue_typed h) splitNames_typed

theorem splitComp_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : CompTyped xi emptyTy (sourceContext nu env) m a) :
    CompTyped xi nu env (splitComp n m) a :=
  substComp_typed (injectComp_typed h) splitNames_typed

theorem splitAdapter_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : AdapterTyped xi emptyTy (sourceContext nu env) adapter a b) :
    AdapterTyped xi nu env (splitAdapter n adapter) a b :=
  substAdapter_typed (injectAdapter_typed h) splitNames_typed

theorem source_recursive_lookup (nu : Fin n → Ty) (env : Context) (s : Fin n) :
    sourceContext nu env s.val = some (nu s) := by
  simp [sourceContext, s.isLt]

theorem source_outer_lookup (nu : Fin n → Ty) (env : Context) (i : Nat) :
    sourceContext nu env (n + i) = env i := by
  simp [sourceContext, Nat.not_lt.mpr (Nat.le_add_right n i)]

theorem split_recursive (s : Fin n) :
    splitNames (R := R) n s.val = .recvar s := by
  simp [splitNames, s.isLt]

theorem split_outer (i : Nat) :
    splitNames (R := R) n (n + i) = .var i := by
  simp [splitNames, Nat.not_lt.mpr (Nat.le_add_right n i)]

/-- The newly bound argument/response/input remains local index zero. -/
theorem split_bound_zero :
    lift (splitNames (R := R) n) 0 = .var 0 := rfl

theorem split_bound_recursive (s : Fin n) :
    lift (splitNames (R := R) n) (s.val + 1) = .recvar s := by
  simp [lift, split_recursive, renameValue]

/-- Closed old values can be captured independently of every fresh node. -/
def CapturesTyped (xi : R → Ty) (env : Context) (capture : Nat → Value R Empty) : Prop :=
  ∀ i a, env i = some a → ValueTyped xi emptyTy emptyContext (capture i) a

def mapOld (f : R → T) (v : Value R Empty) : Value T Empty :=
  closeNamesValue f Empty.elim v

theorem mapOld_typed {xi : R → Ty} {tau : T → Ty}
    (f : R → T) (hf : ∀ r, tau (f r) = xi r)
    (h : ValueTyped xi emptyTy env v a) :
    ValueTyped tau emptyTy env (mapOld f v) a :=
  closeNamesValue_typed h f Empty.elim hf (fun e => Empty.elim e)

def closedCapture (capture : Nat → Value R Empty) : Nat → Value (Sum R S) Empty :=
  fun i => mapOld Sum.inl (capture i)

/-- Recursive names are closed simultaneously, then the independently typed
outer environment is substituted. No new node is used to type the captures. -/
def closeValue (capture : Nat → Value R Empty) (v : Value R S) :
    Value (Sum R S) Empty :=
  substValue (closedCapture capture) (closeNamesValue Sum.inl Sum.inr v)

def closeComp (capture : Nat → Value R Empty) (m : Comp R S) :
    Comp (Sum R S) Empty :=
  substComp (closedCapture capture) (closeNamesComp Sum.inl Sum.inr m)

def closeAdapter (capture : Nat → Value R Empty) (adapter : Adapter R S) :
    Adapter (Sum R S) Empty :=
  substAdapter (closedCapture capture) (closeNamesAdapter Sum.inl Sum.inr adapter)

theorem closedCapture_typed {xi : R → Ty} {nu : S → Ty}
    (hc : CapturesTyped xi env capture) :
    SubstitutionTyped (joinTy xi nu) emptyTy env emptyContext (closedCapture capture) := by
  intro i a hi
  exact mapOld_typed Sum.inl (fun _ => rfl) (hc i a hi)

theorem closeValue_typed {xi : R → Ty} {nu : S → Ty}
    (h : ValueTyped xi nu env v a) (hc : CapturesTyped xi env capture) :
    ValueTyped (joinTy xi nu) emptyTy emptyContext (closeValue capture v) a :=
  substValue_typed
    (closeNamesValue_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

theorem closeComp_typed {xi : R → Ty} {nu : S → Ty}
    (h : CompTyped xi nu env m a) (hc : CapturesTyped xi env capture) :
    CompTyped (joinTy xi nu) emptyTy emptyContext (closeComp capture m) a :=
  substComp_typed
    (closeNamesComp_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

theorem closeAdapter_typed {xi : R → Ty} {nu : S → Ty}
    (h : AdapterTyped xi nu env adapter a b) (hc : CapturesTyped xi env capture) :
    AdapterTyped (joinTy xi nu) emptyTy emptyContext (closeAdapter capture adapter) a b :=
  substAdapter_typed
    (closeNamesAdapter_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

def sourceCloseValue (capture : Nat → Value R Empty) (n : Nat)
    (v : Value R Empty) : Value (Sum R (Fin n)) Empty :=
  closeValue capture (splitValue n v)

def sourceCloseComp (capture : Nat → Value R Empty) (n : Nat)
    (m : Comp R Empty) : Comp (Sum R (Fin n)) Empty :=
  closeComp capture (splitComp n m)

theorem sourceCloseValue_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : ValueTyped xi emptyTy (sourceContext nu env) v a)
    (hc : CapturesTyped xi env capture) :
    ValueTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseValue capture n v) a :=
  closeValue_typed (splitValue_typed h) hc

theorem sourceCloseComp_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : CompTyped xi emptyTy (sourceContext nu env) m a)
    (hc : CapturesTyped xi env capture) :
    CompTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseComp capture n m) a :=
  closeComp_typed (splitComp_typed h) hc

/-- Exact equation from the actual recursive-name constructor to the target
reference, including arbitrarily nested transparent wrappers. -/
theorem frontier_closeNames (f : R → T) (g : S → T) (v : Value R S) :
    nextValue (closeNamesValue f g v) =
      (frontier v).map (Sum.elim f g) := by
  cases v with
  | ref r => rfl
  | recvar s => rfl
  | both v => exact frontier_closeNames f g v
  | top v => exact frontier_closeNames f g v
  | view v o => exact frontier_closeNames f g v
  | wrap v i o => exact frontier_closeNames f g v
  | var i => rfl
  | unit => rfl
  | bool v => rfl
  | int v => rfl
  | floatBits v => rfl
  | string v => rfl
  | bytes v => rfl
  | path v => rfl
  | char v => rfl
  | delay m => rfl
  | inLeft v => rfl
  | inRight v => rfl
  | lambda mode receipt a b c body consumer => rfl

theorem next_mapOld (f : R → T) (v : Value R Empty) :
    nextValue (mapOld f v) = (nextValue v).map f := by
  rw [mapOld, frontier_closeNames]
  unfold nextValue
  cases h : frontier v with
  | none => rfl
  | some r =>
      cases r with
      | inl r => rfl
      | inr e => exact Empty.elim e

theorem projectNode_map (f : R → T) (v : Value R Empty) :
    projectNode (mapOld f v) = (projectNode v).map f := by
  unfold projectNode
  rw [next_mapOld]
  cases nextValue v <;> rfl

def allocate (graph : Graph R) (fresh : S → Value (Sum R S) Empty) : Graph (Sum R S)
  | .inl r => mapOld Sum.inl (graph r)
  | .inr s => fresh s

theorem allocation_old_node (graph : Graph R) (fresh : S → Value (Sum R S) Empty) (r : R) :
    allocate graph fresh (.inl r) = mapOld Sum.inl (graph r) := rfl

theorem allocation_old_type (xi : R → Ty) (nu : S → Ty) (r : R) :
    joinTy xi nu (.inl r) = xi r := rfl

theorem fresh_no_collision (r : R) (s : S) :
    (Sum.inl r : Sum R S) ≠ Sum.inr s := by intro h; cases h

theorem fresh_names_distinct {s t : S} (hne : s ≠ t) :
    (Sum.inr s : Sum R S) ≠ Sum.inr t := by
  intro h
  exact hne (Sum.inr.inj h)

theorem old_no_fresh_edge (graph : Graph R) (fresh : S → Value (Sum R S) Empty)
    (r : R) (s : S) :
    nextValue (allocate graph fresh (.inl r)) ≠ some (.inr s) := by
  change nextValue (mapOld Sum.inl (graph r)) ≠ _
  rw [next_mapOld]
  cases nextValue (graph r) <;> simp

theorem allocate_typed {graph : Graph R} {xi : R → Ty} {nu : S → Ty}
    (hg : WellTyped graph xi) (fresh : S → Value (Sum R S) Empty)
    (hf : ∀ s, ValueTyped (joinTy xi nu) emptyTy emptyContext (fresh s) (nu s)) :
    WellTyped (allocate graph fresh) (joinTy xi nu) := by
  intro r
  cases r with
  | inl r => exact mapOld_typed Sum.inl (fun _ => rfl) (hg r)
  | inr s => exact hf s

/-- Projection commutes with the actual immutable allocation constructor. -/
theorem project_allocation (graph : Graph R) (fresh : S → Value (Sum R S) Empty) :
    projectGraph (allocate graph fresh) =
      GuardedValueGraph.allocate (projectGraph graph) (fun s => projectNode (fresh s)) := by
  funext r
  cases r with
  | inl r => exact projectNode_map Sum.inl (graph r)
  | inr s => rfl

def FreshNoCycle (fresh : Fin n → Value (Sum R (Fin n)) Empty) : Prop :=
  GuardedValueGraph.FiniteDecision.FreshNoCycle (fun s => projectNode (fresh s))

theorem fresh_edge (fresh : Fin n → Value (Sum R (Fin n)) Empty) (s t : Fin n) :
    (GuardedValueGraph.FiniteDecision.freshGraph (fun i => projectNode (fresh i)) s).next = some t ↔
      nextValue (fresh s) = some (.inr t) := by
  rw [GuardedValueGraph.FiniteDecision.freshGraph_edge, projectNode_next]

/-- The finite algorithm computes the local rank from FreshNoCycle, including
fresh-to-old edges; no local rank or typing of projected units is supplied. -/
def allocationGuard {graph : Graph R} (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (fresh : Fin n → Value (Sum R (Fin n)) Empty) (hc : FreshNoCycle fresh) :
    GuardedValueGraph.Guarded (projectGraph (allocate graph fresh)) := by
  rw [project_allocation]
  exact GuardedValueGraph.FiniteDecision.allocateFiniteGuard guard (fun s => projectNode (fresh s)) hc

theorem allocation_guard_iff {graph : Graph R} (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (fresh : Fin n → Value (Sum R (Fin n)) Empty) :
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate graph fresh))) ↔ FreshNoCycle fresh := by
  rw [project_allocation]
  exact GuardedValueGraph.FiniteDecision.allocate_guard_iff guard (fun s => projectNode (fresh s))

def sourceFresh (capture : Nat → Value R Empty) (rhs : Fin n → Value R Empty) :
    Fin n → Value (Sum R (Fin n)) Empty :=
  fun s => sourceCloseValue capture n (rhs s)

/-- Application to GVG-REC-RHS-1: every fresh node's typing is DERIVED from
the actual RHS derivation in the common source recursive context and separately
typed outer captures. The body uses exactly the same simultaneous substitution.
The only guard premise is the actual finite transparent-cycle criterion. -/
theorem source_rec_allocation {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : CompTyped xi emptyTy (sourceContext nu env) body a) :
    WellTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate graph (sourceFresh capture rhs)))) ∧
    CompTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseComp capture n body) a := by
  have hf : ∀ s, ValueTyped (joinTy xi nu) emptyTy emptyContext
      (sourceFresh capture rhs s) (nu s) :=
    fun s => sourceCloseValue_typed (hrhs s) hcapture
  exact ⟨allocate_typed hg _ hf, ⟨allocationGuard guard _ hcycle⟩,
    sourceCloseComp_typed hbody hcapture⟩

/-- The explicit-name source form also allows old graph references in RHS
code. This theorem consumes RHS derivations before closing, not pretyped fresh
nodes. The preceding theorem supplies that premise from the accepted source
grammar by the concrete prefix-splitting translation. -/
theorem named_rec_allocation {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R (Fin n))
    (hrhs : ∀ s, ValueTyped xi nu env (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (fun s => closeValue capture (rhs s)))
    (hbody : CompTyped xi nu env body a) :
    WellTyped (allocate graph (fun s => closeValue capture (rhs s))) (joinTy xi nu) ∧
    Nonempty (GuardedValueGraph.Guarded
      (projectGraph (allocate graph (fun s => closeValue capture (rhs s))))) ∧
    CompTyped (joinTy xi nu) emptyTy emptyContext (closeComp capture body) a :=
  ⟨allocate_typed hg _ (fun s => closeValue_typed (hrhs s) hcapture),
    ⟨allocationGuard guard _ hcycle⟩, closeComp_typed hbody hcapture⟩

/-- For a finite old graph, neither old nor fresh numeric ranks are inputs. -/
theorem finite_source_rec_allocation {graph : Graph (Fin m)}
    {xi : Fin m → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (hOld : GuardedValueGraph.FiniteDecision.NoCycle (projectGraph graph))
    (rhs : Fin n → Value (Fin m) Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : CompTyped xi emptyTy (sourceContext nu env) body a) :
    WellTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate graph (sourceFresh capture rhs)))) ∧
    CompTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseComp capture n body) a :=
  source_rec_allocation hg (GuardedValueGraph.FiniteDecision.guardOfNoCycle _ hOld) rhs hrhs hcapture hcycle hbody


/-- Binder equations expose the lambda consumer's separate outer scope. -/
theorem close_lambda (capture : Nat → Value R Empty)
    (mode receipt a b c body consumer) :
    closeValue (S := S) capture (.lambda mode receipt a b c body consumer) =
      .lambda mode receipt a b c
        (substComp (lift (closedCapture capture))
          (closeNamesComp Sum.inl Sum.inr body))
        (substAdapter (closedCapture capture)
          (closeNamesAdapter Sum.inl Sum.inr consumer)) := rfl

theorem close_adapter (capture : Nat → Value R Empty) (a b body paths views) :
    closeAdapter (S := S) capture (.mk a b body paths views) =
      .mk a b
        (substComp (lift (closedCapture capture))
          (closeNamesComp Sum.inl Sum.inr body)) paths views := rfl

theorem close_request (capture : Nat → Value R Empty) (op payload continuation) :
    closeComp (S := S) capture (.request op payload continuation) =
      .request op (closeValue capture payload)
        (substComp (lift (closedCapture capture))
          (closeNamesComp Sum.inl Sum.inr continuation)) := rfl



def splitHandler (n : Nat) (h : Handler R Empty) : Handler R (Fin n) :=
  substHandler (splitNames n) (injectHandler h)

theorem splitHandler_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : HandlerTyped xi emptyTy (sourceContext nu env) handler a b) :
    HandlerTyped xi nu env (splitHandler n handler) a b :=
  substHandler_typed (injectHandler_typed h) splitNames_typed

def closeHandler (capture : Nat → Value R Empty) (h : Handler R S) :
    Handler (Sum R S) Empty :=
  substHandler (closedCapture capture) (closeNamesHandler Sum.inl Sum.inr h)

theorem closeHandler_typed {xi : R → Ty} {nu : S → Ty}
    (h : HandlerTyped xi nu env handler a b) (hc : CapturesTyped xi env capture) :
    HandlerTyped (joinTy xi nu) emptyTy emptyContext (closeHandler capture handler) a b :=
  substHandler_typed
    (closeNamesHandler_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

def splitValueArms (n : Nat) (arms : ValueArms R Empty) : ValueArms R (Fin n) :=
  substValueArms (splitNames n) (injectValueArms arms)

theorem splitValueArms_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : ValueArmsTyped xi emptyTy (sourceContext nu env) arms a b) :
    ValueArmsTyped xi nu env (splitValueArms n arms) a b :=
  substValueArms_typed (injectValueArms_typed h) splitNames_typed

def closeValueArms (capture : Nat → Value R Empty) (arms : ValueArms R S) :
    ValueArms (Sum R S) Empty :=
  substValueArms (closedCapture capture) (closeNamesValueArms Sum.inl Sum.inr arms)

theorem closeValueArms_typed {xi : R → Ty} {nu : S → Ty}
    (h : ValueArmsTyped xi nu env arms a b) (hc : CapturesTyped xi env capture) :
    ValueArmsTyped (joinTy xi nu) emptyTy emptyContext (closeValueArms capture arms) a b :=
  substValueArms_typed
    (closeNamesValueArms_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

def splitOperationArms (n : Nat) (arms : OperationArms R Empty) : OperationArms R (Fin n) :=
  substOperationArms (splitNames n) (injectOperationArms arms)

theorem splitOperationArms_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : OperationArmsTyped xi emptyTy (sourceContext nu env) arms a b) :
    OperationArmsTyped xi nu env (splitOperationArms n arms) a b :=
  substOperationArms_typed (injectOperationArms_typed h) splitNames_typed

def closeOperationArms (capture : Nat → Value R Empty) (arms : OperationArms R S) :
    OperationArms (Sum R S) Empty :=
  substOperationArms (closedCapture capture) (closeNamesOperationArms Sum.inl Sum.inr arms)

theorem closeOperationArms_typed {xi : R → Ty} {nu : S → Ty}
    (h : OperationArmsTyped xi nu env arms a b) (hc : CapturesTyped xi env capture) :
    OperationArmsTyped (joinTy xi nu) emptyTy emptyContext (closeOperationArms capture arms) a b :=
  substOperationArms_typed
    (closeNamesOperationArms_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)


/-- Fresh-node typing is an output of actual source closure. -/
theorem sourceFresh_typed {xi : R → Ty} {nu : Fin n → Ty}
    (hrhs : ∀ s, ValueTyped xi emptyTy (sourceContext nu env) (rhs s) (nu s))
    (hc : CapturesTyped xi env capture) :
    ∀ s, ValueTyped (joinTy xi nu) emptyTy emptyContext (sourceFresh capture rhs s) (nu s) :=
  fun s => sourceCloseValue_typed (hrhs s) hc

theorem source_allocation_typed {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi)
    (hrhs : ∀ s, ValueTyped xi emptyTy (sourceContext nu env) (rhs s) (nu s))
    (hc : CapturesTyped xi env capture) :
    WellTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu) :=
  allocate_typed hg _ (sourceFresh_typed hrhs hc)

/-- Constructive finite cycle decision; no old-reference equality is required. -/
def freshNoCycleDecidable (fresh : Fin n → Value (Sum R (Fin n)) Empty) :
    Decidable (FreshNoCycle fresh) :=
  GuardedValueGraph.FiniteDecision.noCycleDecidable
    (GuardedValueGraph.FiniteDecision.freshGraph (fun i => projectNode (fresh i)))

/-- Parent application: every RAW finite prefix of the actual closed source body
in its actual source-allocated graph stays typed and can progress. All attempt,
wait, request and continuation forms are included in Prefix without restriction. -/
theorem source_rec_finite_prefix_safety {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : CompTyped xi emptyTy (sourceContext nu env) body a)
    (trace : Prefix (allocate graph (sourceFresh capture rhs))
      (sourceCloseComp capture n body) events last) :
    CompTyped (joinTy xi nu) emptyTy emptyContext last a ∧
      CanProgress (allocate graph (sourceFresh capture rhs)) last :=
  finite_prefix_safety (source_allocation_typed hg hrhs hcapture)
    (allocationGuard guard _ hcycle) (sourceCloseComp_typed hbody hcapture) trace

/-- Zero-step application gives progress of the constructed source body. -/
theorem source_rec_closed_progress {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : CompTyped xi emptyTy (sourceContext nu env) body a) :
    CanProgress (allocate graph (sourceFresh capture rhs)) (sourceCloseComp capture n body) :=
  (source_rec_finite_prefix_safety hg guard rhs hrhs hcapture hcycle hbody (.refl _)).2

/-- The two arm-local variables keep their exact payload/K order. -/
theorem split_arm_payload :
    lift (lift (splitNames (R := R) n)) 0 = .var 0 := rfl

theorem split_arm_originalK :
    lift (lift (splitNames (R := R) n)) 1 = .var 1 := rfl

theorem split_arm_recursive (s : Fin n) :
    lift (lift (splitNames (R := R) n)) (s.val + 2) = .recvar s := by
  simp [lift, split_recursive, renameValue]

theorem close_operation_arm (capture : Nat → Value R Empty)
    (op eligible body rest) :
    closeOperationArms (S := S) capture (.cons op eligible body rest) =
      .cons op eligible
        (substComp (lift (lift (closedCapture capture)))
          (closeNamesComp Sum.inl Sum.inr body))
        (closeOperationArms capture rest) := rfl

theorem close_value_arm (capture : Nat → Value R Empty) (body rest) :
    closeValueArms (S := S) capture (.cons body rest) =
      .cons (substComp (lift (closedCapture capture))
        (closeNamesComp Sum.inl Sum.inr body)) (closeValueArms capture rest) := rfl

theorem close_waitOperation (capture : Nat → Value R Empty) (h op p k rest attempt) :
    closeComp (S := S) capture (.waitOperation h op p k rest attempt) =
      .waitOperation (closeHandler capture h) op (closeValue capture p)
        (substComp (lift (closedCapture capture)) (closeNamesComp Sum.inl Sum.inr k))
        (closeOperationArms capture rest) (closeComp capture attempt) := rfl

theorem close_waitValue (capture : Nat → Value R Empty) (h v rest attempt) :
    closeComp (S := S) capture (.waitValue h v rest attempt) =
      .waitValue (closeHandler capture h) (closeValue capture v)
        (closeValueArms capture rest) (closeComp capture attempt) := rfl

def sourceCloseHandler (capture : Nat → Value R Empty) (n : Nat)
    (handler : Handler R Empty) : Handler (Sum R (Fin n)) Empty :=
  closeHandler capture (splitHandler n handler)

theorem sourceCloseHandler_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : HandlerTyped xi emptyTy (sourceContext nu env) handler a b)
    (hc : CapturesTyped xi env capture) :
    HandlerTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseHandler capture n handler) a b :=
  closeHandler_typed (splitHandler_typed h) hc

def sourceCloseValueArms (capture : Nat → Value R Empty) (n : Nat)
    (arms : ValueArms R Empty) : ValueArms (Sum R (Fin n)) Empty :=
  closeValueArms capture (splitValueArms n arms)

theorem sourceCloseValueArms_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : ValueArmsTyped xi emptyTy (sourceContext nu env) arms a b)
    (hc : CapturesTyped xi env capture) :
    ValueArmsTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseValueArms capture n arms) a b :=
  closeValueArms_typed (splitValueArms_typed h) hc

def sourceCloseOperationArms (capture : Nat → Value R Empty) (n : Nat)
    (arms : OperationArms R Empty) : OperationArms (Sum R (Fin n)) Empty :=
  closeOperationArms capture (splitOperationArms n arms)

theorem sourceCloseOperationArms_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : OperationArmsTyped xi emptyTy (sourceContext nu env) arms a b)
    (hc : CapturesTyped xi env capture) :
    OperationArmsTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseOperationArms capture n arms) a b :=
  closeOperationArms_typed (splitOperationArms_typed h) hc

def sourceCloseAdapter (capture : Nat → Value R Empty) (n : Nat)
    (adapter : Adapter R Empty) : Adapter (Sum R (Fin n)) Empty :=
  closeAdapter capture (splitAdapter n adapter)

theorem sourceCloseAdapter_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : AdapterTyped xi emptyTy (sourceContext nu env) adapter a b)
    (hc : CapturesTyped xi env capture) :
    AdapterTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseAdapter capture n adapter) a b :=
  closeAdapter_typed (splitAdapter_typed h) hc

/-- Existing source references are not reinterpreted as recursive names. -/
theorem sourceClose_old_ref (capture : Nat → Value R Empty) (n : Nat) (r : R) :
    sourceCloseValue capture n (.ref r) = .ref (.inl r) := rfl

theorem sourceClose_recursive (capture : Nat → Value R Empty) (name : Fin n) :
    sourceCloseValue capture n (.var name.val) = .ref (.inr name) := by
  simp only [sourceCloseValue, splitValue, injectValue, substValue, split_recursive,
    closeValue, closeNamesValue]

theorem sourceClose_outer (capture : Nat → Value R Empty) (n i : Nat) :
    sourceCloseValue capture n (.var (n + i)) = mapOld Sum.inl (capture i) := by
  simp only [sourceCloseValue, splitValue, injectValue, substValue, split_outer,
    closeValue, closeNamesValue, closedCapture]

/-- Mapping a shared capture preserves its identity; allocation never copies
one captured address into two fresh addresses. -/
theorem closed_capture_alias_preserved (capture : Nat → Value R Empty)
    (h : capture i = capture j) :
    closedCapture (S := S) capture i = closedCapture capture j :=
  congrArg (mapOld Sum.inl) h

/-- Closure maps the actual shallow K encoding without adding a handler. -/
theorem closeNames_continuation (f : R → T) (q a : Ty) (k : Comp R Empty) :
    mapOld f (continuationValue q a k) =
      continuationValue q a (closeNamesComp f Empty.elim k) := rfl

/-- The separately forwarded HK retains its handler under the response binder. -/
theorem closeNames_forwarded (f : R → T) (h : Handler R Empty) (k : Comp R Empty) :
    closeNamesComp f Empty.elim (forwardedContinuation h k) =
      forwardedContinuation (closeNamesHandler f Empty.elim h) (closeNamesComp f Empty.elim k) := by
  simp only [forwardedContinuation, closeNamesComp, closeNamesHandler_rename]

namespace Examples

def unitTy : Ty := .base .unit
def functionTy : Ty := .callable unitTy unitTy
def receipt : ReceiptTemplate := ⟨[], []⟩
def outer : Context := extend emptyContext unitTy
def oldGraph : Graph (Fin 1) := fun _ => .unit
def oldTypes : Fin 1 → Ty := fun _ => unitTy
def capture : Nat → Value (Fin 1) Empty := fun _ => .ref 0

theorem old_typed : WellTyped oldGraph oldTypes := fun _ => .unit

theorem capture_typed : CapturesTyped oldTypes outer capture := by
  intro i a hi
  cases i with
  | zero =>
      change some unitTy = some a at hi
      cases hi
      exact .ref 0
  | succ i => cases hi

def oldGuard : GuardedValueGraph.Guarded (projectGraph oldGraph) :=
  GuardedValueGraph.FiniteDecision.guardOfNoCycle _
    (GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl))

def operation : OperationInstance := ⟨37, [functionTy], unitTy, unitTy⟩

/-- The selected value arm emits an operation before reporting success. Its
payload and response are two distinct local binders. -/
def requestHandler : Handler R S :=
  .mk 41 unitTy unitTy
    (.cons (.request operation (.var 0) (.ret (.inRight (.var 0)))) .nil) .nil

theorem requestHandler_typed : HandlerTyped xi nu env requestHandler unitTy unitTy :=
  .mk (.cons (.request (.var rfl) (.ret (.inRight (.var rfl)))) .nil) .nil

def other (s : Fin 2) : Fin 2 := if s.val = 0 then 1 else 0

/-- Both source closures have a real handler. The opposite recursive name
occurs in executable body code, and both closures share the old capture. -/
def mutualRhs (s : Fin 2) : Value (Fin 1) Empty :=
  .lambda .computation receipt unitTy unitTy unitTy
    (.handle requestHandler
      (.bind (.ret (.var 3))
        (.dynamicCall (.var ((other s).val + 2)) (.var 1))))
    (.mk unitTy unitTy (.bind (.ret (.var 3)) (.ret (.var 1))) [] [])

theorem mutualRhs_typed (s : Fin 2) :
    ValueTyped oldTypes emptyTy (sourceContext (fun _ : Fin 2 => functionTy) outer)
      (mutualRhs s) functionTy := by
  apply ValueTyped.lambdaComputation
  · apply CompTyped.handle requestHandler_typed
    apply CompTyped.bind (a := unitTy)
    · exact .ret (.var rfl)
    · exact .dynamicCall
        (.var (source_recursive_lookup (fun _ : Fin 2 => functionTy) outer (other s)))
        (.var rfl)
  · exact .mk (.bind (a := unitTy) (.ret (.var rfl)) (.ret (.var rfl)))

def mutualFresh := sourceFresh capture mutualRhs

theorem mutualFresh_equation (s : Fin 2) :
    mutualFresh s =
      .lambda .computation receipt unitTy unitTy unitTy
        (.handle requestHandler
          (.bind (.ret (.ref (.inl 0)))
            (.dynamicCall (.ref (.inr (other s))) (.var 1))))
        (.mk unitTy unitTy
          (.bind (.ret (.ref (.inl 0))) (.ret (.var 1))) [] []) := by
  have hs : s = 0 ∨ s = 1 := by
    have hb := s.isLt
    by_cases hz : s.val = 0
    · exact .inl (Fin.ext hz)
    · exact .inr (Fin.ext (by omega))
  rcases hs with rfl | rfl <;> rfl

theorem mutualFresh_noCycle : FreshNoCycle mutualFresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem mutual_allocation :
    WellTyped (allocate oldGraph mutualFresh) (joinTy oldTypes (fun _ => functionTy)) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate oldGraph mutualFresh))) ∧
    CompTyped (joinTy oldTypes (fun _ => functionTy)) emptyTy emptyContext
      (sourceCloseComp capture 2 (.ret (.var 0))) functionTy :=
  source_rec_allocation old_typed oldGuard mutualRhs mutualRhs_typed capture_typed
    mutualFresh_noCycle (.ret (.var rfl))

/-- An actual source body enters the selected arm with the shared capture. -/
def attemptSource : Comp (Fin 1) Empty := .handle requestHandler (.ret (.var 2))

theorem attemptSource_typed :
    CompTyped oldTypes emptyTy (sourceContext (fun _ : Fin 2 => functionTy) outer)
      attemptSource unitTy := .handle requestHandler_typed (.ret (.var rfl))

def attemptStart : Comp (Sum (Fin 1) (Fin 2)) Empty :=
  .handle requestHandler (.ret (.ref (.inl 0)))

def attemptEnd : Comp (Sum (Fin 1) (Fin 2)) Empty :=
  .request operation (.ref (.inl 0))
    (.waitValue (renameHandler Nat.succ requestHandler) (.ref (.inl 0)) .nil
      (.ret (.inRight (.var 0))))

theorem attempt_source_equation : sourceCloseComp capture 2 attemptSource = attemptStart := rfl

/-- This is an emitted root request during an actual selected-arm attempt,
with the waiting frame retained beneath its response binder. -/
theorem attempt_prefix :
    Prefix (allocate oldGraph mutualFresh) attemptStart [.silent, .silent, .silent] attemptEnd :=
  .cons .handleReturn (.cons .valueCons (.cons .valueRequest (.refl _)))

theorem attempt_prefix_safe :
    CompTyped (joinTy oldTypes (fun _ : Fin 2 => functionTy)) emptyTy emptyContext attemptEnd unitTy ∧
      CanProgress (allocate oldGraph mutualFresh) attemptEnd :=
  source_rec_finite_prefix_safety old_typed oldGuard mutualRhs mutualRhs_typed
    capture_typed mutualFresh_noCycle attemptSource_typed attempt_prefix

/-- Payload0 and originalK1 survive closure, an additional bind, and response.
The arm also reads the same captured old reference used by both lambdas. -/
def originalKArms : OperationArms (Fin 1) Empty :=
  .cons operation true
    (.bind (.ret (.var 4))
      (.request operation (.var 1)
        (.bind (.dynamicCall (.var 3) (.delay (.ret (.var 0))))
          (.ret (.inRight (.var 0)))))) .nil

theorem originalKArms_typed :
    OperationArmsTyped oldTypes emptyTy (sourceContext (fun _ : Fin 2 => functionTy) outer)
      originalKArms unitTy unitTy :=
  .cons (.bind (a := unitTy) (.ret (.var rfl))
    (.request (.var rfl)
      (.bind (a := unitTy) (.dynamicCall (.var rfl) (.delay (.ret (.var rfl))))
        (.ret (.inRight (.var rfl)))))) .nil

theorem originalKArms_closed : sourceCloseOperationArms capture 2 originalKArms =
    .cons operation true
      (.bind (.ret (.ref (.inl 0)))
        (.request operation (.var 1)
          (.bind (.dynamicCall (.var 3) (.delay (.ret (.var 0))))
            (.ret (.inRight (.var 0)))))) .nil := rfl

theorem originalKArms_closed_typed :
    OperationArmsTyped (joinTy oldTypes (fun _ : Fin 2 => functionTy)) emptyTy emptyContext
      (sourceCloseOperationArms capture 2 originalKArms) unitTy unitTy :=
  sourceCloseOperationArms_typed originalKArms_typed capture_typed

/-- Delay stops transparent inspection, while its actual handler body retains
a recursive name underneath the request response and local bind. -/
def delayedRhs : Value (Fin 1) Empty :=
  .delay (.handle requestHandler
    (.request operation (.var 1)
      (.bind (.ret (.var 1)) (.ret (.var 1)))))

theorem delayedRhs_typed :
    ValueTyped oldTypes emptyTy (sourceContext (fun _ : Fin 1 => .thunk unitTy) outer)
      delayedRhs (.thunk unitTy) :=
  .delay (.handle requestHandler_typed (.request (.var rfl)
    (.bind (a := .thunk unitTy) (.ret (.var rfl)) (.ret (.var rfl)))))

theorem delayed_closed : sourceCloseValue capture 1 delayedRhs =
    .delay (.handle requestHandler (.request operation (.ref (.inl 0))
      (.bind (.ret (.ref (.inr 0))) (.ret (.var 1))))) := rfl

theorem delayed_closed_typed :
    ValueTyped (joinTy oldTypes (fun _ : Fin 1 => .thunk unitTy)) emptyTy emptyContext
      (sourceCloseValue capture 1 delayedRhs) (.thunk unitTy) :=
  sourceCloseValue_typed delayedRhs_typed capture_typed

theorem delayed_noCycle : FreshNoCycle (sourceFresh capture (fun _ : Fin 1 => delayedRhs)) :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem delayed_allocation :
    WellTyped (allocate oldGraph (sourceFresh capture (fun _ : Fin 1 => delayedRhs)))
      (joinTy oldTypes (fun _ => .thunk unitTy)) ∧
    Nonempty (GuardedValueGraph.Guarded
      (projectGraph (allocate oldGraph (sourceFresh capture (fun _ : Fin 1 => delayedRhs))))) ∧
    CompTyped (joinTy oldTypes (fun _ : Fin 1 => .thunk unitTy)) emptyTy emptyContext
      (sourceCloseComp capture 1 (.force (.var 0))) unitTy :=
  source_rec_allocation old_typed oldGuard (fun _ : Fin 1 => delayedRhs)
    (fun _ => delayedRhs_typed) capture_typed delayed_noCycle (.force (.var rfl))

/-- Two distinct fresh aliases preserve ONE captured old reference. -/
def sharedAliasRhs : Fin 2 → Value (Fin 1) Empty := fun _ => .var 2
def sharedAliasFresh := sourceFresh capture sharedAliasRhs

theorem sharedAlias_equation (s : Fin 2) : sharedAliasFresh s = .ref (.inl 0) := rfl

theorem sharedAlias_noCycle : FreshNoCycle sharedAliasFresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem sharedAlias_allocation :
    WellTyped (allocate oldGraph sharedAliasFresh) (joinTy oldTypes (fun _ => unitTy)) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate oldGraph sharedAliasFresh))) ∧
    CompTyped (joinTy oldTypes (fun _ => unitTy)) emptyTy emptyContext
      (sourceCloseComp capture 2 (.ret (.var 0))) unitTy :=
  source_rec_allocation old_typed oldGuard sharedAliasRhs (fun _ => .var rfl)
    capture_typed sharedAlias_noCycle (.ret (.var rfl))

def aliasRhs : Fin 1 → Value (Fin 1) Empty := fun _ => .var 0
def aliasFresh := sourceFresh capture aliasRhs

theorem aliasRhs_typed (a : Ty) (s : Fin 1) :
    ValueTyped oldTypes emptyTy (sourceContext (fun _ : Fin 1 => a) outer) (aliasRhs s) a :=
  .var rfl

theorem alias_cycle_rejected : ¬ FreshNoCycle aliasFresh := by
  intro hc
  exact hc 0 (.edge rfl)

theorem alias_allocation_unguarded :
    ¬ Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate oldGraph aliasFresh))) :=
  fun h => alias_cycle_rejected ((allocation_guard_iff oldGuard aliasFresh).mp h)

/-- Evidence wrappers cannot disguise an actual source alias cycle. -/
def topAliasFresh := sourceFresh capture (fun _ : Fin 1 => Value.top (.var 0))

theorem top_alias_cycle_rejected : ¬ FreshNoCycle topAliasFresh := by
  intro hc
  exact hc 0 (.edge rfl)

theorem topAliasRhs_typed :
    ValueTyped oldTypes emptyTy (sourceContext (fun _ : Fin 1 => Ty.top) outer)
      (.top (.var 0)) .top := .top (.var rfl)

/-- Callable adapters do not guard a transparent self-reference. -/
def wrapAliasRhs : Fin 1 → Value (Fin 1) Empty := fun _ =>
  .wrap (.var 0) (.mk unitTy unitTy (.ret (.var 0)) [] [])
    (.mk unitTy unitTy (.ret (.var 0)) [] [])

theorem wrapAliasRhs_typed (s : Fin 1) :
    ValueTyped oldTypes emptyTy (sourceContext (fun _ : Fin 1 => functionTy) outer)
      (wrapAliasRhs s) functionTy :=
  .wrap (.var rfl) (.mk (.ret (.var rfl))) (.mk (.ret (.var rfl)))

theorem wrap_alias_cycle_rejected : ¬ FreshNoCycle (sourceFresh capture wrapAliasRhs) := by
  intro hc
  exact hc 0 (.edge rfl)

end Examples

end YulangClosure.HandlerGraph.Recursive
