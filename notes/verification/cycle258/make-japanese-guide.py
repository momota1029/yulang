from pathlib import Path
import re
v=Path('notes/verification/cycle258');mods=v.joinpath('modules.txt').read_text().splitlines()
scopes=[
'任意の数値名について、有限探索の判定と実I45 lower/upper無限生成族への所属を同値にする。indexより生成名が大きいことと両族の非交差を使う。',
'任意assignmentのlower族の型をslot2、upper族の型をslot4へ置き換える。全段階で同じ関数を使い、初期0〜4、実binderの全成分、全rowを保存する。',
'任意assignmentと任意段階nについて、このfill後にその段階までの実history定義blockがすべて成立する。任意sourceではなく固定I45族である。',
'任意段階n・assignmentについて、fill後のraw/journal意味を有限Viewと同値にする。正段階のjournalに対応するbinder条件を省かない。',
'任意assignmentについて、正段階の有限journal Viewを満たすことと同じfillが全段階journalを満たすことが同値。存在assignmentと全段階の量化は具体的fillで交換する。',
'任意assignmentについて固定type alias/row identityの解釈がfillと一致する。alias表を有限サイズで列挙したという主張ではない。',
'任意段階nについてhistory再生なしのalias compileと展開Viewの意味を接続するが、slot数n+5とordinary数4+16nは増える。',
'任意assignmentについて内部binder型をslot2へ変更してからfillするcompleteを定義。初期0〜4全成分と全rowを保存し、初期rawモデル iff 完成後の全段階journalモデル。',
'任意境界assignmentについて、初期0〜4全成分と全rowを固定する同一assignmentが全段階journalを満たす存在命題 iff 初期rawモデル。内部binder固定を要求しない。',
'提示したbad seedは初期モデルだが内部binderがbottom。旧binderまで固定する強いAgreeでは正段階モデルへ延長不能。任意境界の延長不能ではない。',
'lower包絡が単調で各family indexより小さいという明示前提のもと、早期停止探索 iff 指定fuel区間内の一致。I45の両族へ適用する。',
'任意探索について訪問数≤fuel。対応する生成index iに到達する単独探索は≤i+1。巨大整数演算、名前生成、full fillのlower+upper合計時間は対象外。',
'早期探索版fill/completeは旧関数と関数等号で一致。公開境界と全段階モデル定理をこの等号で継承する。',
'具体252 sourceで任意出力Tyをslot3へ置いても初期raw/journalモデルは保存される。Outputs成立はそのTyが要求Foo(Foo(slot2))と意味同値であることが必要。',
'具体bottom出力で初期モデルとprepared Frameは成立するがOutputs/Holdsは成立しない。Frameだけから出力Evidenceを得る強化を否定する。',
'当該具体packet Inputsは任意assignmentで成立し、Holdsを初期rawモデルとOutputsへ正確に分解する。一般packet全体のInputs定理ではない。',
'任意Viewと任意二assignmentについて、実際に使う型成分および全rowが一致すればModels同値。未使用slot型は除けるがordinary/head RHS/descriptor parameterは追跡する。Step invariantではない。',
'具体252の初期identity Viewで実型supportは0〜2に限られる。slot3型だけを要求出力へ補完しても他の全成分と全rowを保存し、初期rawモデル同値を得る。',
'任意初期rawモデルのslot3補完後に実packet Holdsと既存installation effectのModelsを得る。旧言語Stepを書き換えていない。',
'提示bottom seedには任意payloadのroot Evidenceがない。一方、任意初期rawモデルを補完したassignmentには明示leaf Evidenceを構成できる。',
'任意公開境界について、slot3型だけを解放し他の全成分と全rowを固定するinstalledモデルの存在 iff 元の初期rawモデル。',
'固定の閉じた展開代表の深さは4。任意初期rawモデルの補完後にその代表の意味が成立する。補完前bottomにはEvidenceなし。一般sourceの深さ上界ではない。',
'任意有限basisと任意observerについて、remainingがbasisのsublistである状態をfilterし、実差分のあるwriteだけをStepとする。各Stepでremaining長が厳密減少し全状態Acc。observerの言語的正当性は別の未証明義務。',
'固定I45 fixtureの5事実を提案するobserverについて、初期から一度だけinstallして終端へ達する。二歩不能、全正段階の旧completed state投影は終端。同じ意味の一般inspection実装とはまだ接続していない。',
'任意段階nと公開境界について、旧completed state nと新project nの存在モデルが同値。初期0〜4全成分と全row固定、内部binderは解放。中間subsetの言語的正当性や全microstep simulationは主張しない。',
'任意新Step run長nについて n+終点remaining長≤始点remaining長。初期からbasis長以内、固定I45では1以内。同じproposalのwriteは冪等で次のtryWriteはnone。旧Stepや実時間の上界ではない。'
]
s='# cycle258 宣言の日本語案内\n\n各節はmodule共通の量化範囲・前提・主張。各個別宣言の正確な型（暗黙引数を含む）は `alltypes-final.txt`、公理は `complete-final.txt` を参照。定義・補助補題も省かず列挙する。\n'
for i,(m,scope) in enumerate(zip(mods,scopes),1):
 names=re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M)
 s+=f'\n## {i}. {m}\n\n{scope}\n\n'+', '.join('`'+n+'`' for n in names)+'\n'
v.joinpath('declaration-guide.md').write_text(s)
assert len(mods)==len(scopes)==26
assert sum(len(re.findall(r'^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+(\w+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M)) for m in mods)==200
