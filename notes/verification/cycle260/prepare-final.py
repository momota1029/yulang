from pathlib import Path
import re,json
v=Path('notes/verification/cycle260');mods=v.joinpath('modules.txt').read_text().splitlines();decls=v.joinpath('declarations.txt').read_text().splitlines();imports=''.join('import Yulang.'+m+'\n' for m in mods)
roots=[d.removeprefix('Yulang.') for d in decls if d.split('.')[-1] in ['run_certificate','all_stages','simultaneous_models','public_models','old_new','accepted_models','settle_batch','settle_membership','successful_budget','successful_quiescent','completed_round_simulation','certificate','run_step','closed','loose_initial','version_initial','terminating','no_two','completion','unsupported','same_assignment','final_packet','equation_meaning','all_exact','fact_step_semantic_stutter','target_not_interchangeable','successful','finish_success','class_effects','actual_exact']]
body=Path('lean/Audit/Cycle258Reach.lean').read_text();body=body[body.index('open Lean'):]
body=re.sub(r' let prefixes := .*',' let prefixes := #['+', '.join(json.dumps('Yulang.'+m+'.') for m in mods)+']',body)
body=re.sub(r' let roots := .*',' let roots := #['+', '.join('``Yulang.'+r for r in roots)+']',body)
body=re.sub(r' let explicit := .*',' let explicit := #['+', '.join('``'+d for d in decls)+']',body).replace('CYCLE258','CYCLE260')
Path('lean/Audit/Cycle260Reach.lean').write_text(imports+body)
Path('lean/Audit/Cycle260Types.lean').write_text(imports+''.join('#check @Yulang.'+r+'\n' for r in roots))
Path('lean/Audit/Cycle260AllTypes.lean').write_text(imports+''.join('#check @'+d+'\n' for d in decls))
cache=Path('lean/.lake/cycle260-final');cache.mkdir(exist_ok=True)
for p in Path('lean/.lake/cycle260-focused').rglob('*.olean'):
 rel=p.relative_to('lean/.lake/cycle260-focused')
 if rel.stem in mods:continue
 q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p.resolve())
(cache/'Yulang').mkdir(exist_ok=True)
