from pathlib import Path
import re,json
v=Path('notes/verification/cycle257');mods=v.joinpath('modules.txt').read_text().splitlines();decls=v.joinpath('declarations.txt').read_text().splitlines()
imports=''.join('import Yulang.'+m+'\n' for m in mods)
Path('lean/Audit/Cycle257AllTypes.lean').write_text(imports+'\n'+''.join('#check @'+d+'\n' for d in decls))
roots=['GeneralDictionaryUpperHistory257.block_in_source','GeneralPresenceIdempotentTree257.equivalent','GeneralDictionaryOrdinaryCanonical257.exact','GeneralDictionaryFiveSlot257.models_exact','GeneralDictionaryFiniteView257.terms_finite','GeneralDictionaryNoModelRefinement257.initial_public_models','GeneralDictionaryProjectionBoundary257.distinct_with_same_view','GeneralDictionaryKnownProjection257.preserved','GeneralDictionaryPointProjection257.preserved','GeneralDictionaryReportProjection257.actual_report','GeneralDictionaryBinderGap257.current_raw_not_journal','GeneralDictionaryBinderFact257.all_past_fits','GeneralDictionaryPastPacket257.holds','GeneralDictionaryJournalRepair257.exact','GeneralDictionaryFiniteJournal257.public_models','GeneralDictionaryFiniteJournal257.stable','GeneralDictionaryFiniteJournal257.ordinary_bound']
body=Path('lean/Audit/Cycle256Reach.lean').read_text();body=body[body.index('import Lean'):]
body=re.sub(r' let prefixes := .*',' let prefixes := #['+', '.join(json.dumps('Yulang.'+m+'.') for m in mods)+']',body)
body=re.sub(r' let roots := .*',' let roots := #['+', '.join('``Yulang.'+r for r in roots)+']',body)
body=re.sub(r' let explicit := .*',' let explicit := #['+', '.join('``'+d for d in decls)+']',body).replace('CYCLE256','CYCLE257')
Path('lean/Audit/Cycle257Reach.lean').write_text(imports+body)
Path('lean/Audit/Cycle257Types.lean').write_text(imports+'\n'+''.join('#check @Yulang.'+d+'\n' for d in roots))
cache=Path('lean/.lake/cycle257-final');cache.mkdir(exist_ok=True)
for directory in ['lean/.lake/cycle257-critical','lean/.lake/cycle257-focused']:
 for p in Path(directory).rglob('*.olean'):
  rel=p.relative_to(directory)
  if rel.stem in mods or rel.stem.startswith('Cycle257'):continue
  q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():q.symlink_to(p.resolve())
(cache/'Yulang').mkdir(exist_ok=True);(cache/'Audit').mkdir(exist_ok=True)
print('fresh final outputs prepared for',len(mods),'modules')
