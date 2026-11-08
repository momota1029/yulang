import Yulang.CommonRoleOutermostResolver
import Yulang.CommonRoleUnaryGraphBridge
import Yulang.CommonRoleRecordGraphBridge
import Yulang.CommonRoleCandidateConstraints
import Yulang.CommonRoleStablePaterson

/-! A settled unary fragment: known arguments retain equal endpoint pairs;
missing lower heads defer. Structural self loops are finite graphs, not
finite approximations. Named declarations remain opaque. No associated
updates, open record tails, multiple arguments or non-singleton intervals. -/
namespace Yulang.CommonRoleSettledSyntax
open CommonRoleRegularGraph CommonRoleGraphBisimulation
open CommonRoleCaptureNormalization (Form)

inductive Constructor where
  | variant (tag : Nat)
  | record (label : Nat)
  | nominal (name : Nat)
  deriving DecidableEq, Repr

def Constructor.node (c : Constructor) (child : Fin n) : Node n :=
  match c with
  | .variant tag => .structural (2 * tag) [child]
  | .record label => .structural (2 * label + 1) [child]
  | .nominal name => .nominal name [child]

inductive Atom where
  | int
  | named (name : Nat)
  deriving DecidableEq, Repr

inductive Ty where
  | unknown
  | atom (a : Atom)
  | wrap (c : Constructor) (payload : Ty)
  | variantLoop (tag : Nat)
  | recordLoop (label : Nat)
  deriving DecidableEq, Repr

def Ty.nodes : Ty → Nat
  | .wrap _ t => t.nodes + 1
  | _ => 1

theorem Ty.nodes_pos (t : Ty) : 0 < t.nodes := by cases t <;> simp [Ty.nodes]

def Ty.root (t : Ty) : Fin t.nodes := ⟨0, t.nodes_pos⟩

def Node.shift : Node n → Node (n + 1)
  | .unresolved => .unresolved
  | .scalar a => .scalar a
  | .structural c cs => .structural c (cs.map Fin.succ)
  | .nominal c cs => .nominal c (cs.map Fin.succ)

def Ty.graph : (t : Ty) → Graph t.nodes
  | .unknown => fun _ => .unresolved
  | .atom .int => fun _ => .scalar 0
  | .atom (.named name) => fun _ => .nominal name []
  | .wrap c t => Fin.cases (c.node t.root.succ) (fun i => Node.shift (t.graph i))
  | .variantLoop tag => fun _ => .structural (2 * tag) [⟨0, by simp [Ty.nodes]⟩]
  | .recordLoop label => fun _ => .structural (2 * label + 1) [⟨0, by simp [Ty.nodes]⟩]

def Ty.regular (t : Ty) : Bool := regularAt t.graph t.root
def Ty.Regular (t : Ty) : Prop := RegularAt t.graph t.root

theorem regular_exact (t : Ty) : t.regular = true ↔ t.Regular := regular_at_exact _ _

theorem loop_regular (tag : Nat) : (Ty.variantLoop tag).regular = true ∧
    (Ty.recordLoop tag).regular = true := by
  constructor <;> apply (regular_exact _).mpr <;> apply Or.inl
  all_goals refine ⟨_, [⟨0, by simp [Ty.nodes]⟩], rfl, ⟨0, by simp [Ty.nodes]⟩, by simp, ?_⟩
  all_goals exact .nil _

@[simp] theorem unknown_not_regular : Ty.unknown.regular = false := rfl
@[simp] theorem atom_not_regular (a : Atom) : (Ty.atom a).regular = false := by cases a <;> rfl

/-- A regular graph is an opaque leaf for the measure; K2 forbids opening it. -/
def Ty.form : Ty → Form
  | .wrap _ t => .tick t.form
  | _ => .int

def Ty.weight (t : Ty) : Nat := t.form.encode.size

@[simp] theorem form_normal (t : Ty) : t.form.normalize = t.form := by
  induction t <;> simp_all [Ty.form, Form.normalize]

inductive Pattern where
  | bind (first : Nat) (more : List Nat)
  | atom (a : Atom)
  | wrap (c : Constructor) (p : Pattern)
  deriving DecidableEq, Repr

def Pattern.names : Pattern → List Nat
  | .bind first more => first :: more
  | .atom _ => []
  | .wrap _ p => p.names

def mergedForm (first : Nat) : List Nat → Form
  | [] => .var first
  | next :: rest => .join (.var first) (mergedForm next rest)

def Pattern.form : Pattern → Form
  | .bind first more => mergedForm first more
  | .atom _ => .int
  | .wrap _ p => .tick p.form

inductive Template where
  | var (name : Nat)
  | atom (a : Atom)
  | wrap (c : Constructor) (t : Template)
  deriving DecidableEq, Repr

def Template.names : Template → List Nat
  | .var name => [name]
  | .atom _ => []
  | .wrap _ t => t.names

def Template.form : Template → Form
  | .var name => .var name
  | .atom _ => .int
  | .wrap _ t => .tick t.form

/-- Every head name captures the same whole payload. Admission checks every
used name before this substitution; no missing-name fallback is observable. -/
def Template.instantiate (payload : Ty) : Template → Ty
  | .var _ => payload
  | .atom a => .atom a
  | .wrap c t => .wrap c (t.instantiate payload)

theorem template_form (t : Template) (payload : Ty) :
    (t.instantiate payload).form = (t.form.subst (fun _ => payload.form)).normalize := by
  induction t <;> simp_all [Template.instantiate, Template.form, Ty.form, Form.subst, Form.normalize]

theorem merged_form_subst (first : Nat) (more : List Nat) (t : Ty) :
    ((mergedForm first more).subst (fun _ => t.form)).normalize = t.form := by
  induction more generalizing first with
  | nil => simp [mergedForm, Form.subst]
  | cons next rest ih => simp [mergedForm, Form.subst, Form.normalize, ih]

inductive Observation where
  | hit (payload : Ty)
  | mismatch
  | deferred
  | blocked
  deriving DecidableEq, Repr

/-- A literal binds no names. Its sentinel is never used by a variable. -/
def inspect : Pattern → Ty → Observation
  | .bind _ _, t => .hit t
  | .atom expected, t =>
      if t.regular then .blocked else
      match t with
      | .unknown => .deferred
      | .atom actual => if expected = actual then .hit .unknown else .mismatch
      | _ => .mismatch
  | .wrap c p, t =>
      if t.regular then .blocked else
      match t with
      | .unknown => .deferred
      | .wrap d v => if c = d then inspect p v else .mismatch
      | _ => .mismatch

/-- Independent rules refer to graph regularity, never to `inspect`. -/
inductive Inspect : Pattern → Ty → Observation → Prop where
  | bind : Inspect (.bind first more) t (.hit t)
  | atom_cycle : t.Regular → Inspect (.atom a) t .blocked
  | wrap_cycle : t.Regular → Inspect (.wrap c p) t .blocked
  | atom_unknown : Inspect (.atom a) .unknown .deferred
  | wrap_unknown : Inspect (.wrap c p) .unknown .deferred
  | atom_hit : Inspect (.atom a) (.atom a) (.hit .unknown)
  | atom_other : a ≠ b → Inspect (.atom a) (.atom b) .mismatch
  | atom_wrap : ¬ (Ty.wrap c t).Regular → Inspect (.atom a) (.wrap c t) .mismatch
  | wrap_atom : Inspect (.wrap c p) (.atom a) .mismatch
  | wrap_other : ¬ (Ty.wrap d t).Regular → c ≠ d →
      Inspect (.wrap c p) (.wrap d t) .mismatch
  | wrap_hit : ¬ (Ty.wrap c t).Regular → Inspect p t result →
      Inspect (.wrap c p) (.wrap c t) result

theorem inspect_sound (p : Pattern) (t : Ty) : Inspect p t (inspect p t) := by
  induction p generalizing t with
  | bind => exact .bind
  | atom a =>
      simp only [inspect]
      split
      · exact .atom_cycle ((regular_exact _).mp ‹_›)
      · rename_i nr
        have notRegular : ¬ t.Regular := fun h => nr ((regular_exact _).mpr h)
        cases t with
        | unknown => exact .atom_unknown
        | atom b =>
            change Inspect _ _ (if a = b then .hit .unknown else .mismatch)
            split <;> rename_i h
            · subst b; exact .atom_hit
            · exact .atom_other h
        | wrap c v => exact .atom_wrap notRegular
        | variantLoop tag => exact False.elim (nr (loop_regular tag).1)
        | recordLoop label => exact False.elim (nr (loop_regular label).2)
  | wrap c p ih =>
      simp only [inspect]
      split
      · exact .wrap_cycle ((regular_exact _).mp ‹_›)
      · rename_i nr
        have notRegular : ¬ t.Regular := fun h => nr ((regular_exact _).mpr h)
        cases t with
        | unknown => exact .wrap_unknown
        | atom a => exact .wrap_atom
        | wrap d v =>
            change Inspect _ _ (if c = d then inspect p v else .mismatch)
            split <;> rename_i h
            · subst d; exact .wrap_hit notRegular (ih v)
            · exact .wrap_other notRegular h
        | variantLoop tag => exact False.elim (nr (loop_regular tag).1)
        | recordLoop label => exact False.elim (nr (loop_regular label).2)

theorem regular_false {t : Ty} (h : ¬ t.Regular) : t.regular = false :=
  Bool.eq_false_iff.mpr (mt (regular_exact _).mp h)

theorem inspect_complete (h : Inspect p t result) : inspect p t = result := by
  induction h with
  | bind => rfl
  | atom_cycle h => simp [inspect, (regular_exact _).mpr h]
  | wrap_cycle h => simp [inspect, (regular_exact _).mpr h]
  | atom_unknown | wrap_unknown | atom_hit | wrap_atom => simp [inspect]
  | atom_other h => simp [inspect, h]
  | atom_wrap h => simp [inspect, regular_false h]
  | wrap_other h different => simp [inspect, different, regular_false h]
  | wrap_hit h _ ih => simp [inspect, ih, regular_false h]

theorem inspect_exact (p : Pattern) (t : Ty) (result : Observation) :
    inspect p t = result ↔ Inspect p t result :=
  ⟨fun h => h ▸ inspect_sound p t, inspect_complete⟩

theorem hit_form (h : Inspect p t (.hit payload)) :
    (p.form.subst (fun _ => payload.form)).normalize = t.form := by
  generalize resultEq : Observation.hit payload = result at h
  induction h with
  | bind => cases resultEq; exact merged_form_subst _ _ _
  | atom_hit => cases resultEq; rfl
  | wrap_hit _ _ ih =>
      simp only [Pattern.form, Form.subst, Form.normalize, Ty.form]
      exact congrArg Form.tick (ih resultEq)
  | _ => cases resultEq

structure Declaration where
  role : Nat
  key : Nat
  head : Pattern
  requirements : List (Nat × Template)
  deriving DecidableEq, Repr

def Declaration.stable (d : Declaration) : CommonRoleStablePaterson.Declaration :=
  ⟨d.role, d.key, [d.head.form], d.requirements.map (fun r => (r.1, [r.2.form]))⟩

def Declaration.check (d : Declaration) : Bool :=
  CommonRoleStablePaterson.check d.stable &&
    d.requirements.all (fun r => r.2.names.all (fun name => decide (name ∈ d.head.names)))

theorem checked_names (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements) :
    ∀ name ∈ r.2.names, name ∈ d.head.names := by
  have h := (Bool.and_eq_true_iff.mp checked).2
  simpa only [List.all_eq_true, decide_eq_true_eq] using (List.all_eq_true.mp h r member)

def bindings (p : Pattern) (payload : Ty) : List (Nat × (Ty × Ty)) :=
  p.names.eraseDups.map (fun name => (name, (payload, payload)))

theorem every_where_bound (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements) (payload : Ty)
    (name : Nat) (used : name ∈ r.2.names) :
    (name, (payload, payload)) ∈ bindings d.head payload := by
  exact List.mem_map.mpr ⟨name, by simpa using checked_names d checked r member name used, rfl⟩

/-- Declaration-derived descent for every generated child, including K2
children. No assumed rank, late check, depth bound or successful-child premise. -/
theorem checked_child_decreases (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements)
    (t payload : Ty) (matched : Inspect d.head t (.hit payload)) :
    (r.2.instantiate payload).weight < t.weight := by
  have accepted := (Bool.and_eq_true_iff.mp checked).1
  have strict := (CommonRoleStablePaterson.check_sound d.stable accepted
    (r.1, [r.2.form]) (List.mem_map.mpr ⟨r, member, rfl⟩) (fun _ => payload.form)).1
  simpa only [Declaration.stable, CommonRoleStablePaterson.instantiated, List.map_cons,
    List.map_nil, Roles.argsSize, Nat.add_zero, hit_form matched, ← template_form,
    Ty.weight] using strict
theorem binding_lookup (p : Pattern) (payload : Ty) (name : Nat) :
    CommonRoleCanonicalRows.lookup name (bindings p payload) =
      if name ∈ p.names then some (payload, payload) else none := by
  simpa only [bindings, List.mem_eraseDups] using
    CommonRoleSharedPayloadCapture.lookup_repeated_payload p.names.eraseDups (payload, payload) name

/-- Named lookup specification for both substituted endpoints. -/
inductive Substitute (env : List (Nat × (Ty × Ty))) : Template → Ty → Prop where
  | var : CommonRoleCanonicalRows.lookup name env = some (t, t) → Substitute env (.var name) t
  | atom : Substitute env (.atom a) (.atom a)
  | wrap : Substitute env template t → Substitute env (.wrap c template) (.wrap c t)

theorem substitute_all_names (p : Pattern) (payload : Ty) (template : Template)
    (bound : ∀ name ∈ template.names, name ∈ p.names) :
    Substitute (bindings p payload) template (template.instantiate payload) := by
  induction template with
  | var name =>
      apply Substitute.var
      simp [binding_lookup, bound name (by simp [Template.names]), Template.instantiate]
  | atom => exact .atom
  | wrap c t ih => exact .wrap (ih bound)

theorem every_where_substituted (d : Declaration) (checked : d.check = true)
    (r : Nat × Template) (member : r ∈ d.requirements) (payload : Ty) :
    Substitute (bindings d.head payload) r.2 (r.2.instantiate payload) :=
  substitute_all_names d.head payload r.2 (checked_names d checked r member)

end Yulang.CommonRoleSettledSyntax
