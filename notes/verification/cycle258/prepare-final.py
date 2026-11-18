from pathlib import Path
import re,json
v=Path('notes/verification/cycle258');mods=v.joinpath('modules.txt').read_text().splitlines();decls=v.joinpath('declarations.txt').read_text().splitlines();imports=''.join('import Yulang.'+m+'\n' for m in mods)
roots=['GeneralDictionaryUniformJournal258.all_stages','GeneralDictionarySourceExtension258.exchange','GeneralDictionaryPrivateBoundary258.retained_binder_impossible','GeneralDictionaryFastFill258.complete_eq','GeneralDictionaryOutputEvidence258.completed_evidence','GeneralDictionaryOutputPublic258.public_models','GeneralRebaseStep258.accessible','GeneralDictionaryRebaseStep258.no_two_steps','GeneralDictionaryRebasePublic258.old_new']
# Use actual exported names for roots, avoiding guessed labels.
roots=[x for x in roots if 'Yulang.'+x in decls]
roots+=['GeneralDictionaryCompletedReadback258.'+d.split('.')[-1] for d in decls if d.startswith('Yulang.GeneralDictionaryCompletedReadback258.')]
body=Path('lean/Audit/Cycle257Reach.lean').read_text();body=body[body.index('open Lean'):]
body=re.sub(r' let prefixes := .*',' let prefixes := #['+', '.join(json.dumps('Yulang.'+m+'.') for m in mods)+']',body)
body=re.sub(r' let roots := .*',' let roots := #['+', '.join('``Yulang.'+r for r in roots)+']',body)
body=re.sub(r' let explicit := .*',' let explicit := #['+', '.join('``'+d for d in decls)+']',body).replace('CYCLE257','CYCLE258')
Path('lean/Audit/Cycle258Reach.lean').write_text(imports+body)
Path('lean/Audit/Cycle258Types.lean').write_text(imports+''.join('#check @Yulang.'+r+'\n' for r in roots))
Path('lean/Audit/Cycle258AllTypes.lean').write_text(imports+''.join('#check @'+d+'\n' for d in decls))
cache=Path('lean/.lake/cycle258-final');cache.mkdir(exist_ok=True)
for p in Path('lean/.lake/cycle258-focused').rglob('*.olean'):
 rel=p.relative_to('lean/.lake/cycle258-focused')
 if rel.stem in mods:continue
 q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p.resolve())
(cache/'Yulang').mkdir(exist_ok=True)
