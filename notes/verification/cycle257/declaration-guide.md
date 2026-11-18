# cycle257 宣言案内

全引数は各コード型に記したとおり全称量化される。日本語の共通条件と個別説明を合わせて読む。完全な elaborated 型は [alltypes-final.txt](alltypes-final.txt)。固定の実I45 family以外への一般化は明記した箇所だけ。

## GeneralDictionaryUpperHistory257

任意の段階 n。実 I45 family の lower/upper 定義を replay 順に並べる。各追加方程式と全 block は実 ordinary に含まれ、target は初期名0〜4より大きい。初期名の展開は恒等。

### `upperEntry`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def upperEntry (n : Nat) : Entry Nat
```

### `lowerEntry`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def lowerEntry (n : Nat) : Entry Nat
```

### `history`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def history : Nat → List (Entry Nat)
```

### `upper_equations`

当該upper方程式の実ordinary包含。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem upper_equations (n : Nat) :
 GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4)) ⊆ atoms (n+1)
```

### `block_in_source`

履歴全blockの実ordinary包含。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem block_in_source (n : Nat) : block (history n) ⊆ atoms n
```

### `targets_above`

各targetは初期領域より大きい。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem targets_above (n : Nat) (e : Entry Nat) (member : e ∈ history n) : 4 < e.1
```

### `initial_fixed`

初期名の値を固定。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem initial_fixed (n name : Nat) (small : name ≤ 4) :
 (mapping (history n) name).ty = .var name
```

## GeneralDictionaryFullExpansion257

任意 n,index。lower は index≤n、upper は index<n の範囲で、実 ordered mapping の全過去展開を計算する。lower は var2 の二重 union 木、upper は inter(var4,var4)。snoc_other だけは任意 entries/name で追加targetとの不一致が前提。

### `snoc_other`

他targetの追加は対象の展開を変えない。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem snoc_other (entries : List (Entry Nat)) (e : Entry Nat) (name : Nat)
 (different : e.1 ≠ name) : (mapping (entries ++ [e]) name).ty = (mapping entries name).ty
```

### `current_lower`

最新lowerの展開を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem current_lower (n : Nat) : (mapping (history n) (lower n)).ty = tree n
```

### `past_lower`

全過去lowerの展開を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem past_lower (n index : Nat) (before : index ≤ n) :
 (mapping (history n) (lower index)).ty = tree index
```

### `current_upper`

最新upperの展開を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem current_upper (n : Nat) :
 (mapping (history (n+1)) (upper n)).ty = .inter (.var 4) (.var 4)
```

### `past_upper`

全過去upperの展開を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem past_upper (n index : Nat) (before : index < n) :
 (mapping (history n) (upper index)).ty = .inter (.var 4) (.var 4)
```

## GeneralPresenceIdempotentTree257

任意の型項と任意 Assignment。両子を再帰縮約し、構文的に同じ子だけ union/inter から除く。Common の join/meet と全構成子の合同則により意味同値。row は変えず、一般の有限正規形や分配則は主張しない。atom/list の Holds/All も同値。

### `join`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def join (a b : TyTerm Nat) : TyTerm Nat
```

### `meet`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def meet (a b : TyTerm Nat) : TyTerm Nat
```

### `reduce`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def reduce : TyTerm Nat → TyTerm Nat
```

### `meet_self`

同じ値のintersectionはその値と意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem meet_self (value : Ty) : Equivalent (.inter value value) value
```

### `join_exact`

重複unionの局所縮約は意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem join_exact (a b : TyTerm Nat) (assignment : Assignment) :
 Equivalent ((join a b).eval model assignment) ((TyTerm.union a b).eval model assignment)
```

### `meet_exact`

重複intersectionの局所縮約は意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem meet_exact (a b : TyTerm Nat) (assignment : Assignment) :
 Equivalent ((meet a b).eval model assignment) ((TyTerm.inter a b).eval model assignment)
```

### `equivalent`

再帰縮約の全割当での意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem equivalent (term : TyTerm Nat) (assignment : Assignment) :
 Equivalent ((reduce term).eval model assignment) (term.eval model assignment)
```

### `atom`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def atom : PresenceNormalForm.Atom Nat → PresenceNormalForm.Atom Nat
```

### `atom_exact`

atom単位のHolds同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem atom_exact (value : PresenceNormalForm.Atom Nat) (assignment : Assignment) :
 (atom value).Holds model assignment ↔ value.Holds model assignment
```

### `all_exact`

リスト全体のAll同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem all_exact (values : List (PresenceNormalForm.Atom Nat)) (assignment : Assignment) :
 PresenceNormalForm.All model assignment (values.map atom) ↔ PresenceNormalForm.All model assignment values
```

## GeneralDictionaryOrdinaryShape257

任意の実段階 n。追加 ordinary のリストを cross4、両側等式8、selfChecks4に厳密分解する。全過去 atom は index<n の4種類のいずれかで、累積リスト長は16n。

### `crossAtom`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def crossAtom (n : Nat) : Atom Nat
```

### `selfAtom`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def selfAtom : Atom Nat
```

### `lowerAtoms`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def lowerAtoms (n : Nat)
```

### `upperAtoms`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def upperAtoms (n : Nat)
```

### `added_exact`

実追加リストの完全な式。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem added_exact (n : Nat) : GeneralNominalVersionedInstallation231.atoms (packet n) =
 [crossAtom n,crossAtom n,crossAtom n,crossAtom n] ++
 (lowerAtoms n ++ upperAtoms n ++ (lowerAtoms n ++ upperAtoms n)) ++
 [selfAtom,selfAtom,crossAtom n,crossAtom n]
```

### `atom_cases`

実atomの過去stage別分類。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem atom_cases (n : Nat) (atom : Atom Nat) (member : atom ∈ atoms n) :
 ∃ index, index < n ∧
 (atom = crossAtom index ∨ atom = selfAtom ∨ atom ∈ lowerAtoms index ∨ atom ∈ upperAtoms index)
```

### `length_atoms`

実累積リスト長16n。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem length_atoms (n : Nat) : (atoms n).length = 16*n
```

## GeneralDictionaryFullReduced257

任意 n,index。lower index≤n、upper index<n の正確な展開を両極性縮約すると初期var2/4。初期名はname≤4で固定。逆極性の旧prepareはupper展開に失敗するが、縮約後はvar4として成功。失敗は内部adapterのnoneであり言語拒否ではない。

### `reduce_tree`

重複union木をvar2へ縮約。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem reduce_tree (n : Nat) : reduce (tree n) = .var 2
```

### `lower_fixed`

lower式の縮約を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem lower_fixed (n index : Nat) (before : index ≤ n) :
 reduce (mapping (history n) (lower index)).ty = .var 2
```

### `upper_fixed`

upper式の縮約を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem upper_fixed (n index : Nat) (before : index < n) :
 reduce (mapping (history n) (upper index)).ty = .var 4
```

### `initial_fixed`

初期名の値を固定。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem initial_fixed (n name : Nat) (small : name ≤ 4) :
 reduce (mapping (history n) name).ty = .var name
```

### `lower_adapter_failure`

一方向prepareの逆極性失敗を明示。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem lower_adapter_failure (n index : Nat) (before : index < n) :
 GeneralPresenceCheckedNormal252.prepare .lower [.var 0,.var 1,.var 2,.var 3,.var 4]
   (mapping (history n) (upper index)).ty = none
```

### `repaired_upper_prepare`

両極性縮約後のprepare成功。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem repaired_upper_prepare (n index : Nat) (before : index < n) :
 GeneralPresenceCheckedNormal252.prepare .lower [.var 0,.var 1,.var 2,.var 3,.var 4]
   (reduce (mapping (history n) (upper index)).ty) = some (.var 4)
```

## GeneralDictionaryOrdinaryFinite257

任意 n と実 atoms n の各atom。履歴展開と両極性縮約で、2≤4、3≤3、2≤2、4≤4の4候補に入る。個別lower/upper補題はindex<n、crossはindex≤n。写像だけでは長さ16nは変わらない。

### `rewriteAtom`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def rewriteAtom (n : Nat) (atom : Atom Nat) : Atom Nat
```

### `le`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def le (a b : Nat) : Atom Nat
```

### `candidates`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def candidates : List (Atom Nat)
```

### `cross_fixed`

cross atomの固定形。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem cross_fixed (n index : Nat) (before : index ≤ n) :
 rewriteAtom n (crossAtom index) = le 2 4
```

### `self_fixed`

self atomの固定形。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem self_fixed (n : Nat) : rewriteAtom n selfAtom = le 3 3
```

### `lower_fixed`

lower式の縮約を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem lower_fixed (n index : Nat) (before : index < n) (atom : Atom Nat)
 (member : atom ∈ lowerAtoms index) : rewriteAtom n atom = le 2 2
```

### `upper_fixed`

upper式の縮約を計算。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem upper_fixed (n index : Nat) (before : index < n) (atom : Atom Nat)
 (member : atom ∈ upperAtoms index) : rewriteAtom n atom = le 4 4
```

### `finite`

実atomの4候補所属。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem finite (n : Nat) (atom : Atom Nat) (member : atom ∈ atoms n) : rewriteAtom n atom ∈ candidates
```

### `rewritten`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def rewritten (n : Nat) : List (Atom Nat)
```

### `rewritten_finite`

全書換列の4候補包含。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem rewritten_finite (n : Nat) : rewritten n ⊆ candidates
```

### `length_rewritten`

書換だけでは16n長は変わらない。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem length_rewritten (n : Nat) : (rewritten n).length = 16*n
```

## GeneralDictionaryOrdinaryCanonical257

任意 n。n>0で4候補すべてが実 rewritten に存在する。空の初期列／以後4候補という compact は元のmembershipとAllを厳密に保ち、長さ≤4。任意source一般化や新Stepは含まない。

### `all_present`

正段階で全4候補が現れる。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem all_present (n : Nat) (positive : 0 < n) : candidates ⊆ rewritten n
```

### `compact`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def compact (n : Nat) : List (Atom Nat)
```

### `membership`

compactと元列のmembership iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem membership (n : Nat) (atom : Atom Nat) : atom ∈ compact n ↔ atom ∈ rewritten n
```

### `exact`

当該moduleが扱う意味判定の厳密同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem exact (n : Nat) (assignment : GeneralNominalCommonBridge.Assignment) :
 All CommonNominalFullCarrier.model assignment (compact n) ↔
 All CommonNominalFullCarrier.model assignment (rewritten n)
```

### `length_bound`

compact列の長さ上界。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem length_bound (n : Nat) : (compact n).length ≤ 4
```

### `stable`

正段階のliteral表現または射影の安定。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem stable (n : Nat) : compact (n+1) = candidates
```

## GeneralDictionaryCompactView257

任意 n,Assignment。全型consumerの縮約と累積ordinaryの4候補化を行い、base ordinaryは保持。expandedとのModels iffは全割当で無条件。元rawの同一割当復元は実history block成立が必要。無条件対応はsolve後のraw。公開射影は段階依存hidden targets以外の全Compと全rowを固定する存在量化。slotsはn+5。

### `expanded`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def expanded (n : Nat) : View
```

### `normalized`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def normalized (n : Nat) : View
```

### `baseAtoms`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def baseAtoms (n : Nat) : List (Atom Nat)
```

### `compact`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def compact (n : Nat) : View
```

### `normalized_exact`

全型consumer縮約のModels iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem normalized_exact (n : Nat) (assignment : Assignment) :
 (normalized n).Models assignment ↔ (expanded n).Models assignment
```

### `ordinary_split`

base部分と累積部分の厳密分解。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem ordinary_split (n : Nat) : (normalized n).ordinary =
 baseAtoms n ++ GeneralDictionaryOrdinaryFinite257.rewritten n
```

### `compact_exact`

compactとexpandedのModels iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem compact_exact (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔ (expanded n).Models assignment
```

### `compact_solved`

solve後の元rawとの無条件Models iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem compact_solved (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔ GeneralNominalState.Models (context n).state
   (solve model (history n) assignment)
```

### `recovered`

block成立の下で同一割当のraw Modelsを回収。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem recovered (n : Nat) (assignment : Assignment)
 (valid : All model assignment (GeneralPresenceDefinitionRewrite244.block (history n))) :
 (compact n).Models assignment ↔ GeneralNominalState.Models (context n).state assignment
```

### `hidden`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def hidden (n : Nat) : List Nat
```

### `public_models`

指定公開成分を固定した存在モデル射影iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ assignment, GeneralNominalRebasePublicModel242.PublicAgree (hidden n) assignment boundary ∧
   GeneralNominalState.Models (context n).state assignment) ↔
 (∃ assignment, GeneralNominalRebasePublicModel242.PublicAgree (hidden n) assignment boundary ∧
   (compact n).Models assignment)
```

### `hidden_above`

hiddenの各名は初期領域より大きい。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem hidden_above (n name : Nat) (member : name ∈ hidden n) : 4 < name
```

### `slot_count`

slot数の正確な値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem slot_count (n : Nat) : (compact n).slots = n+5
```

## GeneralDictionaryCompactFields257

任意 n と実slot。初期slotは自分のvar、追加slotはvar2。Foo/Pair descriptorの型引数を正確に計算し、heads/intervalsは空。base ordinaryは初期0/1のint等式4atomで固定。

### `slot_type`

各slot型の正確な代表。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem slot_type (n : Nat) (slot : Fin (n+5)) :
 ((compact n).slot slot).ty = .var (representative slot)
```

### `foo`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def foo : Descriptor
```

### `pair`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def pair : Descriptor
```

### `original_type`

初期slot型の保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem original_type (n : Nat) (slot : Fin 5) :
 reduce (mapping (history n) (source n (original n slot))).ty = .var slot.val
```

### `anchor_type`

anchor型のvar2への縮約。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem anchor_type (n : Nat) :
 reduce (mapping (history n) (source n (anchor n))).ty = .var 2
```

### `foo_descriptor`

Foo descriptorの正確な式。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem foo_descriptor (n : Nat) :
 GeneralNominalViewTypeMap255.descriptor reduce
 (GeneralNominalRebaseRawView243.descriptor (GeneralDictionaryLooseFamilyBase240.base n) (mapping (history n))
 (GeneralDictionaryLooseFamilyBase240.foo n)) = foo
```

### `pair_descriptor`

Pair descriptorの正確な式。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem pair_descriptor (n : Nat) :
 GeneralNominalViewTypeMap255.descriptor reduce
 (GeneralNominalRebaseRawView243.descriptor (GeneralDictionaryLooseFamilyBase240.base n) (mapping (history n))
 (GeneralDictionaryLooseFamilyBase240.pair n)) = pair
```

### `nominal`

全slotのnominal分類。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem nominal (n : Nat) (slot : Fin (n+5)) : (compact n).nominals slot =
 if slot.val = 3 then some pair else if slot.val = 2 ∨ 4 ≤ slot.val then some foo else none
```

### `no_heads`

head列は空。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem no_heads (n : Nat) (slot : Fin (n+5)) : (compact n).heads slot = none
```

### `no_intervals`

interval列は空。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem no_intervals (n : Nat) : (compact n).intervals = []
```

### `baseFacts`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def baseFacts : List (Atom Nat)
```

### `base_fixed`

baseの4atomは固定。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem base_fixed (n : Nat) : baseAtoms n = baseFacts
```

### `ordinary`

ordinary全列の正確な式。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem ordinary (n : Nat) : (compact n).ordinary = baseFacts ++ GeneralDictionaryOrdinaryCanonical257.compact n
```

## GeneralDictionaryFiveSlot257

任意 n,Assignment。具体的なI45 field分類により追加slotを初期slot2に写す。compactと5slot Viewは全割当でModels同値。後者は初期／正段階の2種類で、ordinaryは最大8。一般のsource Stateを再構成する定理ではない。

### `descriptor`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def descriptor (name : Nat) : Option Descriptor
```

### `projection`

実過去reportのProjectionModelsを構成。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def projection (slot : Fin (n+5)) : Fin 5
```

### `view`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def view (n : Nat) : View
```

### `original_projection`

初期slotはprojectionで自分に戻る。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem original_projection (n : Nat) (index : Fin 5) : projection (original n index) = index
```

### `projected_descriptor`

projectionでdescriptor分類を保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem projected_descriptor (slot : Fin (n+5)) : descriptor (projection slot).val = descriptor slot.val
```

### `compact_nominal`

compactと5slot側nominalを対応付ける。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem compact_nominal (n : Nat) (slot : Fin (n+5)) :
 (compact n).nominals slot = (view n).nominals (projection slot)
```

### `compact_target`

対応するslot型はliteral等しい。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem compact_target (n : Nat) (slot : Fin (n+5)) :
 ((compact n).slot slot).ty = ((view n).slot (projection slot)).ty
```

### `models_exact`

対象表現間の全割当Models iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem models_exact (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔ (view n).Models assignment
```

### `stable`

正段階のliteral表現または射影の安定。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem stable (n : Nat) : view (n+1) = view 1
```

### `five_slots`

slot数は5。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem five_slots (n : Nat) : (view n).slots = 5
```

### `ordinary_bound`

ordinary長の一様上界。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem ordinary_bound (n : Nat) : (view n).ordinary.length ≤ 8
```

## GeneralDictionaryInitialProjection257

任意 n と公開Assignment。固定の初期0〜4の全Compと全rowを保つAgreeを使い、rawと5slot Viewの存在モデル射影を同値にする。逆方向はhistoryをsolveする。正段階では射影が安定。

### `Agree`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def Agree (internal boundary : Assignment) : Prop
```

### `solve_agrees`

solveは指定の公開成分を保つ。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem solve_agrees (n : Nat) (internal boundary : Assignment) (same : Agree internal boundary) :
 Agree (solve model (history n) internal) boundary
```

### `public_models`

指定公開成分を固定した存在モデル射影iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ internal, Agree internal boundary ∧ GeneralNominalState.Models (context n).state internal) ↔
 (∃ internal, Agree internal boundary ∧ (GeneralDictionaryFiveSlot257.view n).Models internal)
```

### `stable`

正段階のliteral表現または射影の安定。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem stable (n : Nat) (boundary : Assignment) :
 (∃ internal, Agree internal boundary ∧ GeneralNominalState.Models (context (n+1)).state internal) ↔
 (∃ internal, Agree internal boundary ∧ GeneralNominalState.Models (context 1).state internal)
```

## GeneralDictionaryFiniteView257

任意 n。5slot quotient全型consumerは初期5変数とintの6項内で、任意sideのprepareが同じ項で成功。name>4のprivate type readなし。slot.rowは初期indexのvar。Viewだけを見る任意Nat rankは旧完了cycleごとに真に減れない。

### `pool`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def pool : List (TyTerm Nat)
```

### `two_views`

Viewは初期/正段階の2値のみ。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem two_views (n : Nat) : view n = view 0 ∨ view n = view 1
```

### `terms_finite`

全型consumerが固定pool内。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem terms_finite (n : Nat) : GeneralNominalViewTypeTerms255.terms (view n) ⊆ pool
```

### `atoms_fixed`

両sideのprepareが同じ型項を返す。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem atoms_fixed (n : Nat) (side : GeneralPresenceCheckedNormal252.Side) (term : TyTerm Nat)
 (present : term ∈ GeneralNominalViewTypeTerms255.terms (view n)) :
 GeneralPresenceCheckedNormal252.prepare side pool term = some term
```

### `no_private_type_reads`

private type名を読まない。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem no_private_type_reads (n name : Nat) (privateName : 4 < name) (term : TyTerm Nat)
 (present : term ∈ GeneralNominalViewTypeTerms255.terms (view n)) : name ∉ typeSources term
```

### `row_metadata`

slotのrow metadataの正確な式。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem row_metadata (n : Nat) (index : Fin 5) : ((view n).slot index).row = .var index.val
```

### `no_strict_view_rank`

ViewだけのNat rankによる旧cycleごとの厳密減少は不可能。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem no_strict_view_rank (rank : GeneralNominalRebaseRawView243.View → Nat) :
 ¬ ∀ n, rank (view (n+2)) < rank (view (n+1))
```

## GeneralDictionaryNoModelRefinement257

任意Assignment。初期ViewのPair descriptorから2≤4を導く（2と4を同一名にはしない）。追加4事実は初期モデルで既に成立し、全nのView.Modelsは初期と同値。rawの固定初期Comp＋全row存在射影も全nで初期と同値。

### `initial_cross`

初期Pairの意味から2≤4を導く。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem initial_cross (assignment : Assignment) (valid : (view 0).Models assignment) :
 Subtype (assignment 2).1 (assignment 4).1
```

### `initial_facts`

初期モデルで4事実が成立。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem initial_facts (assignment : Assignment) (valid : (view 0).Models assignment) :
 All model assignment candidates
```

### `one_iff_zero`

stage1/0のView.Models iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem one_iff_zero (assignment : Assignment) :
 (view 1).Models assignment ↔ (view 0).Models assignment
```

### `all_iff_zero`

全nのView.Modelsは初期と同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem all_iff_zero (n : Nat) (assignment : Assignment) :
 (view n).Models assignment ↔ (view 0).Models assignment
```

### `initial_public_models`

固定初期公開射影は初期rawと同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem initial_public_models (n : Nat) (boundary : Assignment) :
 (∃ internal, GeneralDictionaryInitialProjection257.Agree internal boundary ∧
   GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state internal) ↔
 (∃ internal, GeneralDictionaryInitialProjection257.Agree internal boundary ∧
   GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context 0).state internal)
```

## GeneralDictionaryProjectionBoundary257

任意 n。実anchor(n+1)と初期slot2は異なるがprojectionで等しくなるので非単射。実stateのslot数はn+5、a≠bならstate a≠state b。異なる実stateが同じ正段階Viewを持つ。

### `anchor_distinct`

実anchorと初期slot2は異なる。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem anchor_distinct (n : Nat) : anchor (n+1) ≠ original (n+1) 2
```

### `anchor_collapsed`

異なる実slotをprojectionが同一化する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem anchor_collapsed (n : Nat) : projection (anchor (n+1)) = projection (original (n+1) 2)
```

### `not_injective`

projectionの非単射性。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem not_injective (n : Nat) : ¬ Function.Injective (@projection (n+1))
```

### `state_slots`

実stateのslot数n+5。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem state_slots (n : Nat) : (state n).core.erased.current.context.state.base.slots = n+5
```

### `states_distinct`

異なるindexの実stateは異なる。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem states_distinct (a b : Nat) (different : a ≠ b) : state a ≠ state b
```

### `distinct_with_same_view`

実stateは異なるが正段階Viewは同じ。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem distinct_with_same_view (n : Nat) :
 state (n+1) ≠ state (n+2) ∧ view (n+1) = view (n+2)
```

## GeneralDictionaryKnownProjection257

known_slotは任意raw Stateとslotでsource写像の単射性を使う一般補題。残りはI45具体familyで、Knownはslot.val≥2と同値。その判定は初期slot代表へのprojectionで保存される。

### `known_slot`

Knownをsource単射性により当該slotへ局所化。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem known_slot (raw : GeneralNominalState.State) (slot : Fin raw.base.slots) :
 GeneralNominalState.Known raw (raw.base.source slot) ↔
 (raw.view.graph slot ≠ .unresolved ∨ ∃ descriptor, raw.nominals slot = some descriptor)
```

### `classified`

具体familyの判定を算術条件へ分類。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem classified (n : Nat) (slot : Fin (n+5)) :
 GeneralNominalState.Known (context n).state (source n slot) ↔ 2 ≤ slot.val
```

### `projection_threshold`

projectionはKnownの閾値判定を保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem projection_threshold (slot : Fin (n+5)) : 2 ≤ (projection slot).val ↔ 2 ≤ slot.val
```

### `preserved`

当該判定を実slotと初期代表の間で保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem preserved (n : Nat) (slot : Fin (n+5)) :
 GeneralNominalState.Known (context n).state (source n slot) ↔
 GeneralNominalState.Known (context 0).state (projection slot).val
```

## GeneralDictionaryPointProjection257

任意 n。Foo descriptorは点、Pairは非点。実slotのPointAtはslot.val=2またはslot.val≥4と同値で、初期代表へのprojectionで保存。任意inspection一般化はしない。

### `foo_point`

Fooはpoint descriptor。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem foo_point (n : Nat) : PointDescriptor (foo n)
```

### `pair_nonpoint`

Pairは非point descriptor。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem pair_nonpoint (n : Nat) : ¬ PointDescriptor (pair n)
```

### `classified`

具体familyの判定を算術条件へ分類。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem classified (n : Nat) (slot : Fin (n+5)) :
 PointAt (context n).state slot ↔ slot.val=2 ∨ 4 ≤ slot.val
```

### `projected_kind`

projectionはpoint分類を保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem projected_kind (slot : Fin (n+5)) :
 (projection slot).val=2 ∨ 4 ≤ (projection slot).val ↔ slot.val=2 ∨ 4 ≤ slot.val
```

### `preserved`

当該判定を実slotと初期代表の間で保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem preserved (n : Nat) (slot : Fin (n+5)) :
 PointAt (context n).state slot ↔ PointAt (context 0).state (projection slot)
```

## GeneralDictionaryReportProjection257

任意 n。実packet nのReport全fieldをslot projectionで運ぶと実packet0のReportにliteral一致する。origin pathsは変更しない。任意packetや任意rebaseのsimulationは主張しない。

### `bounds`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
abbrev bounds (n : Nat) (pair : GeneralNominalInspection.Bounds (context n).state) :
 GeneralNominalInspection.Bounds (context 0).state
```

### `transport`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def transport (n : Nat) (report : Report (context n).state) : Report (context 0).state
```

### `anchor_projected`

anchorの初期slot2への写像。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem anchor_projected (n : Nat) : projection (anchor n) = (2 : Fin 5)
```

### `actual_report`

実report全体のtransport後のliteral一致。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem actual_report (n : Nat) :
 transport n (GeneralNominalPacketSupport.report (packet n)) =
 GeneralNominalPacketSupport.report (packet 0)
```

### `origins_unchanged`

captureのorigin列を保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem origins_unchanged (n : Nat) :
 ((GeneralNominalPacketSupport.report (packet n)).captures.map (fun capture => capture.origin)) =
 ((GeneralNominalPacketSupport.report (packet 0)).captures.map (fun capture => capture.origin))
```

## GeneralDictionaryBinderGap257

任意 n。実current rawモデルを満たす明示witnessは、初期モデルの固定purpose8 actual binderだけbottomへ変え、両側historyをsolveしたもの。index<nの過去Inputsに違反し、n+1のjournal Modelsを満たさない。到達性はstateの性質であり、この割当がjournalモデルのまま遷移したとは言わない。

### `seed`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
noncomputable def seed : Assignment
```

### `witness`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
noncomputable def witness (n : Nat) : Assignment
```

### `actual_above`

固定actual binderは初期名より大きい。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem actual_above : 4 < actual
```

### `seed_initial`

binder変更seedは初期成分を保存。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem seed_initial (name : Nat) (small : name ≤ 4) : seed name = model name
```

### `seed_models`

binderをbottomにしたseedも初期journalモデル。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem seed_models : GeneralNominalVersionedJournal232.Models initial seed
```

### `raw_witness`

witnessは実current rawモデル。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem raw_witness (n : Nat) : GeneralNominalState.Models (context n).state (witness n)
```

### `actual_outside`

actual binderはhistory target外。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem actual_outside (n : Nat) (entry : GeneralPresenceDefinitionRewrite244.Entry Nat)
 (member : entry ∈ history n) : entry.1 ≠ actual
```

### `actual_bottom`

witnessのactual binder型はbottom。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem actual_bottom (n : Nat) : (witness n actual).1 = .bottom
```

### `lower_value`

witnessのlower型はFoo(Int)と意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem lower_value (n index : Nat) (before : index ≤ n) :
 Equivalent (witness n (lower index)).1 F
```

### `not_inputs`

過去Inputsの不成立。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem not_inputs (n index : Nat) (before : index < n) :
 ¬ GeneralNominalVersionedPlans231.Inputs (plan index) (witness n)
```

### `not_journal`

正段階journal Modelsの不成立。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem not_journal (n : Nat) :
 ¬ GeneralNominalVersionedJournal232.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)) (witness (n+1))
```

### `current_raw_not_journal`

実到達stateでrawとjournalの意味差を具体化。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem current_raw_not_journal (n : Nat) :
 GeneralNominalState.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)).core.erased.current.context.state (witness (n+1)) ∧
 ¬ GeneralNominalVersionedJournal232.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)) (witness (n+1))
```

## GeneralDictionaryHistoricalValues257

任意 n,Assignment、実current raw Modelsが前提。初期raw Modelsを同一割当で回収し、index≤nのlowerはsource2、index<nのupperはsource4と意味同値。source2と4も意味同値だがliteral名は区別する。atoms_monoはa≤bで実ordinary包含。

### `raw_initial`

current rawから同一割当の初期rawを回収。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem raw_initial (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment
```

### `atoms_mono`

実ordinaryの段階間包含。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem atoms_mono (a b : Nat) (before : a ≤ b) : atoms a ⊆ atoms b
```

### `lower_same`

過去lowerはsource2と意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem lower_same (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 Equivalent (assignment (lower index)).1 (assignment 2).1
```

### `upper_same`

過去upperはsource4と意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem upper_same (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 Equivalent (assignment (upper index)).1 (assignment 4).1
```

### `source_pair`

source2/4の意味同値（名は別）。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem source_pair (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 Equivalent (assignment 2).1 (assignment 4).1
```

## GeneralDictionaryBinderFact257

任意 n,Assignment。実current raw Modelsの下、0< nなら固定actual binder≃source2の2atomが全index<nのcapture-center Fitsと同値。各Inputs／正段階journalはこの事実を要求する。反例witnessはこの事実に違反する。fullInputsの十分性は別module。

### `facts`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def facts : List (Atom Nat)
```

### `Holds`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def Holds (assignment : Assignment) : Prop
```

### `facts_exact`

固定2atomとbinderの意味同値条件を同一視。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem facts_exact (assignment : Assignment) : All model assignment facts ↔ Holds assignment
```

### `fits_exact`

過去capture Fitsと固定binder事実のiff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem fits_exact (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalCaptureMerges.Fits assignment (lower (index+1),upper index) (assignment actual).1 ↔ Holds assignment
```

### `all_past_fits`

全過去capture Fitsと固定binder事実のiff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem all_past_fits (n : Nat) (positive : 0 < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 (∀ index, index < n → GeneralNominalCaptureMerges.Fits assignment
   (lower (index+1),upper index) (assignment actual).1) ↔ Holds assignment
```

### `input_requires`

過去Inputsは固定binder事実を要求。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem input_requires (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (input : GeneralNominalVersionedPlans231.Inputs (plan index) assignment) : Holds assignment
```

### `journal_requires`

正段階journalは固定binder事実を要求。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem journal_requires (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)) assignment) : Holds assignment
```

### `excludes_gap`

固定binder事実は反例witnessを除外。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem excludes_gap (n : Nat) : ¬ Holds (GeneralDictionaryBinderGap257.witness (n+1))
```

### `facts_length`

固定binder事実は2atom。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem facts_length : facts.length = 2
```

## GeneralDictionaryPastRaw257

任意 n,index,Assignment、実current raw Modelsが前提。index≤nなら過去raw Models、index<nなら実packetのOrdinaryを同一割当で回収する。

### `raw_past`

過去raw Modelsを回収。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem raw_past (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalState.Models (context index).state assignment
```

### `ordinary_past`

過去packet Ordinaryを回収。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem ordinary_past (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 GeneralNominalVersionedPlans231.Ordinary (packet index) assignment
```

## GeneralDictionaryPastObservations257

任意Assignmentの初期source Modelsから、root3の2つのnominal引数の観測存在とFoo(Int)との意味同値を導く。実current raw Modelsとindex≤nなら過去endpointのFitsとReportのProjectionModelsを再構成する。

### `observed`

実rootのnominal引数観測を構成。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem observed (assignment : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment)
 (index : Nat) (small : index < 2) : Observes assignment (.nominal (.source 3) 5 index) F
```

### `observed_value`

観測値のFoo(Int)との意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem observed_value (assignment : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment)
 (index : Nat) (small : index < 2) (value : Ty)
 (seen : Observes assignment (.nominal (.source 3) 5 index) value) : Equivalent value F
```

### `endpoint_fit`

過去端点で観測値のFitsを構成。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem endpoint_fit (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) (value : Ty)
 (same : Equivalent value F) : GeneralNominalCaptureMerges.Fits assignment (lower index,4) value
```

### `projection`

実過去reportのProjectionModelsを構成。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem projection (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 ProjectionModels (context index).state (GeneralNominalPacketSupport.report (packet index)) assignment
```

## GeneralDictionaryPastPacket257

任意 n,index,Assignment、実current raw Modelsと固定binder事実が前提。head_schemaは任意indexで成立し、index<nなら実planのHolds全項（raw、ordinary、report、schema、capture、空emission/children）を構成する。このterminal family限定。

### `actual_value`

binder値はFoo(Int)と意味同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem actual_value (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) : Equivalent (assignment actual).1 F
```

### `head_schema`

実過去head schemaの意味を構成。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem head_schema (n index : Nat) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) :
 GeneralNominalVersionedPlans231.SchemaHolds (plan index) (plan index).headSchema assignment
```

### `holds`

実過去packet Holds全項を構成。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem holds (n index : Nat) (before : index < n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) :
 GeneralNominalVersionedPlans231.Holds (plan index) assignment
```

## GeneralDictionaryJournalRepair257

任意 n,index,Assignment、実current raw Modelsとbinder事実からindex≤nの過去journal Modelsを再構成。正段階state(n+1)ではjournal Models iff current raw Models∧binder事実が同一割当で成立。新Stepや停止性は主張しない。

### `earlier_journal`

実過去journal Modelsを構成。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem earlier_journal (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) : Models (state index) assignment
```

### `exact`

当該moduleが扱う意味判定の厳密同値。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem exact (n : Nat) (assignment : Assignment) :
 Models (state (n+1)) assignment ↔
 GeneralNominalState.Models (context (n+1)).state assignment ∧
 GeneralDictionaryBinderFact257.Holds assignment
```

## GeneralDictionaryFiniteJournal257

任意正段階n+1。5slot Viewに固定binder2atomを保持し、最大10ordinary。全journalとの無条件同値はsolve(history(n+1))後の割当。固定初期0〜4＋actual binderの全Compと全rowを保つ存在射影も同値。literal Viewは正段階で一定。view0はbinder追加済みなので初期journal同値は主張しない。再構成history自体の大きさは有限化していない。

### `view`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def view (n : Nat) : View
```

### `models_exact`

対象表現間の全割当Models iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem models_exact (n : Nat) (assignment : Assignment) :
 (view n).Models assignment ↔
 (GeneralDictionaryFiveSlot257.view n).Models assignment ∧ GeneralDictionaryBinderFact257.Holds assignment
```

### `solve_binder`

solveは固定binder事実の真偽を保つ。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem solve_binder (n : Nat) (assignment : Assignment) :
 GeneralDictionaryBinderFact257.Holds (solve model (history n) assignment) ↔ GeneralDictionaryBinderFact257.Holds assignment
```

### `solved_exact`

有限Viewとsolve後の全journal Modelsのiff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem solved_exact (n : Nat) (assignment : Assignment) :
 (view (n+1)).Models assignment ↔
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1))
   (solve model (history (n+1)) assignment)
```

### `Agree`

このmoduleの共通条件で用いる具体的な表現・判定を定義する。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
def Agree (internal boundary : Assignment) : Prop
```

### `solve_agrees`

solveは指定の公開成分を保つ。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem solve_agrees (n : Nat) (internal boundary : Assignment) (same : Agree internal boundary) :
 Agree (solve model (history n) internal) boundary
```

### `public_models`

指定公開成分を固定した存在モデル射影iff。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ internal, Agree internal boundary ∧
   GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) internal) ↔
 (∃ internal, Agree internal boundary ∧ (view (n+1)).Models internal)
```

### `stable`

正段階のliteral表現または射影の安定。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem stable (n : Nat) : view (n+1) = view 1
```

### `ordinary_bound`

ordinary長の一様上界。 上記の共通対象・範囲と、次の明示前提の下で読む。

```lean
theorem ordinary_bound (n : Nat) : (view n).ordinary.length ≤ 10
```
