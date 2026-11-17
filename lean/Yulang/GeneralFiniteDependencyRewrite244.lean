import Std
/-! A sufficient condition for finite-support inlining: a rank decreases on
source dependencies. No producer for actual language steps is assumed proved,
and dependency accessibility is not solver transition accessibility. -/
namespace Yulang.GeneralFiniteDependencyRewrite244
variable {Name : Type}

def Below (rank : Name → Nat) (owner : Name) (sources : List Name) : Prop :=
 ∀ source ∈ sources, rank source < rank owner

def RewriteBelow (rank : Name → Nat) (substitution : Name → List Name) : Prop :=
 ∀ name source, source ∈ substitution name → rank source ≤ rank name

def expand (substitution : Name → List Name) (sources : List Name) : List Name :=
 sources.flatMap substitution

theorem below_expand (safe : RewriteBelow rank substitution) (before : Below rank owner sources) :
 Below rank owner (expand substitution sources) := by
 intro source member
 obtain ⟨old,oldMem,newMem⟩ := List.mem_flatMap.mp member
 exact Nat.lt_of_le_of_lt (safe old source newMem) (before old oldMem)

theorem expand_pool (old : sources ⊆ pool)
 (replacement : ∀ name ∈ pool, substitution name ⊆ pool) : expand substitution sources ⊆ pool := by
 intro name member
 obtain ⟨source,present,inReplacement⟩ := List.mem_flatMap.mp member
 exact replacement source (old present) inReplacement

def mapping [DecidableEq Name] (targets : List Name) (replacement : Name → List Name) : Name → List Name :=
 fun name => if name ∈ targets then replacement name else [name]

theorem mapping_below [DecidableEq Name] (targets : List Name) (replacement : Name → List Name)
 (ranked : ∀ name ∈ targets, Below rank name (replacement name)) :
 RewriteBelow rank (mapping targets replacement) := by
 intro name source member
 by_cases inside : name ∈ targets
 · have present : source ∈ replacement name := by simpa [mapping,inside] using member
   exact Nat.le_of_lt (ranked name inside source present)
 · have same : source = name := by simpa [mapping,inside] using member
   subst source; exact Nat.le_refl _

theorem no_self (safe : Below rank owner sources) : owner ∉ sources :=
 fun present => Nat.lt_irrefl _ (safe owner present)

theorem rewrite_no_self [DecidableEq Name] {rank : Name → Nat} {targets sources : List Name}
 {replacement : Name → List Name} {owner : Name}
 (ranked : ∀ name ∈ targets, Below rank name (replacement name)) (before : Below rank owner sources) :
 owner ∉ expand (mapping targets replacement) sources :=
 no_self (below_expand (mapping_below targets replacement ranked) before)

abbrev Table (Name : Type) := List (Name × List Name)
def Ranked (rank : Name → Nat) (table : Table Name) : Prop :=
 ∀ entry ∈ table, Below rank entry.1 entry.2

def rewrite (substitution : Name → List Name) (table : Table Name) : Table Name :=
 table.map (fun entry => (entry.1,expand substitution entry.2))

theorem ranked_rewrite (safe : RewriteBelow rank substitution) (before : Ranked rank table) :
 Ranked rank (rewrite substitution table) := by
 intro entry member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact below_expand safe (before original present)

def Edge (table : Table Name) (source owner : Name) : Prop :=
 ∃ entry ∈ table, entry.1 = owner ∧ source ∈ entry.2

theorem edge_decreases (ranked : Ranked rank table) (edge : Edge table source owner) : rank source < rank owner := by
 obtain ⟨entry,member,equal,present⟩ := edge
 exact equal ▸ ranked entry member source present

theorem dependency_accessible (ranked : Ranked rank table) (owner : Name) : Acc (Edge table) owner := by
 have all (n : Nat) : ∀ owner, rank owner = n → Acc (Edge table) owner := by
   intro owner equal
   induction n using Nat.strongRecOn generalizing owner with
   | ind n ih =>
     apply Acc.intro
     intro source edge
     exact ih (rank source) (equal ▸ edge_decreases ranked edge) source rfl
 exact all (rank owner) owner rfl

theorem rewritten_dependency_accessible (safe : RewriteBelow rank substitution)
 (ranked : Ranked rank table) (owner : Name) : Acc (Edge (rewrite substitution table)) owner :=
 dependency_accessible (ranked_rewrite safe ranked) owner
end Yulang.GeneralFiniteDependencyRewrite244
