from pathlib import Path
import re,json
v=Path('notes/verification/cycle263');mods=v.joinpath('modules.txt').read_text().splitlines();decls=v.joinpath('declarations.txt').read_text().splitlines()
roots=[d for d in decls if d.split('.')[-1] in ['exact','reference_eq','requests_eq','certificate','source_certificate','actual_requests','all_requests','source_observer','source_step_models','table_unchanged','meaning_unchanged','class_effects_unchanged','transport','of_report_data','step_actual','error_selected','successful','run_exact','check_exact','outcome','selected_provenance','nonempty_success','success_not_satisfiability','strict_weakening','run_bound','cuts_length','checked_certificate','source_outcome','source_bounds','source_compatible_from_heads','representative_compatible','source_layout','source_compatible','terminal_not_done','actual_write','write_exact','run_success','nontrivial']]
s=Path('lean/Audit/Cycle261Reach.lean').read_text();s=s[s.index('open Lean'):]
s=re.sub(r' let prefixes := .*',' let prefixes := #['+', '.join(json.dumps('Yulang.'+m+'.') for m in mods)+']',s)
s=re.sub(r' let roots := .*',' let roots := #['+', '.join('``'+d for d in roots)+']',s)
s=re.sub(r' let explicit := .*',' let explicit := #['+', '.join('``'+d for d in decls)+']',s).replace('CYCLE261','CYCLE263')
Path('lean/Audit/Cycle263Reach.lean').write_text(''.join('import Yulang.'+m+'\n' for m in mods)+s)
print('selected roots',len(roots))
