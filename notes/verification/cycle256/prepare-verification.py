from pathlib import Path
import re,json
v=Path('notes/verification/cycle256'); mods=v.joinpath('modules.txt').read_text().splitlines(); decls=v.joinpath('declarations.txt').read_text().splitlines()
old=Path('lean/Audit/Cycle255Reach.lean').read_text(); body=old[old.index('import Lean'):]
body=re.sub(r' let prefixes := .*', ' let prefixes := #['+', '.join(json.dumps('Yulang.'+m+'.') for m in mods)+']',body)
roots=['GeneralNominalInitialAggregate256.prepared','GeneralNominalInitialAggregate256.fits','GeneralNominalHistoricalAggregate256.fits_exact','GeneralDictionaryAggregateHistory256.prepared','GeneralDictionaryAggregateBasis256.prepared_source_fits','GeneralDictionaryAggregateBasis256.initial_basis','GeneralDictionaryAggregateBasis256.pool_private_free','GeneralDictionaryAggregateRows256.row_read_retained','GeneralDictionaryAggregateRows256.row_name_private','GeneralDictionaryAggregateRows256.slot_rows_irrelevant','GeneralDictionaryHistoricalFields256.slot_prepared','GeneralDictionarySlotView256.public_models','GeneralDictionarySlotView256.source_erased_rows','GeneralDictionarySlotView256.slot_values_finite']
body=re.sub(r' let roots := .*',' let roots := #['+', '.join('``Yulang.'+r for r in roots)+']',body)
body=re.sub(r' let explicit := .*',' let explicit := #['+', '.join('``'+d for d in decls)+']',body).replace('CYCLE255','CYCLE256')
Path('lean/Audit/Cycle256Reach.lean').write_text(''.join('import Yulang.'+m+'\n' for m in mods)+body)
checks=['GeneralNominalInputOccurrences256.frame_nonempty','GeneralNominalInitialAggregate256.prepared','GeneralNominalHistoricalAggregate256.fits_exact','GeneralDictionaryAggregateHistory256.prepared','GeneralDictionaryReachableAggregate256.fits_exact','GeneralDictionarySlotView256.public_models','GeneralDictionarySlotView256.compact_solved']
Path('lean/Audit/Cycle256Types.lean').write_text(''.join('import Yulang.'+m+'\n' for m in mods)+'\n'+''.join('#check @Yulang.'+d+'\n' for d in checks))
cache=Path('lean/.lake/cycle256-focused');cache.mkdir(exist_ok=True)
for p in Path('lean/.lake/cycle247-clean').rglob('*.olean'):
 rel=p.relative_to('lean/.lake/cycle247-clean')
 if rel.stem in mods or rel.stem.startswith('Cycle256'):continue
 q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p.resolve())
(cache/'Yulang').mkdir(exist_ok=True);(cache/'Audit').mkdir(exist_ok=True)
print('Prepared fresh cycle256 outputs; older cache links retained')
