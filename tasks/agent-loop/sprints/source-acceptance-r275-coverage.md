# R275 constructor coverage — source-view preparation only

This table records the acceptance-to-candidate call spine and the owner of
each visible forwarding step. It is not a derivation of fixture behavior.
Every successful return remains a premise for Sol to check against the bounded source view. Omitted source behavior is unknown.

| Caller/callsite | Actual callee/owner | View excerpt | Required normal-return premise |
|---|---|---|---|
| Fixture datum constructs one `Arc<SourceText>` and passes a clone to `parse_file`, while moving the original into `scan_header` | `scan_header` → `header::discover_header` → `HeaderDiscovery::into_header_info` | R274-E001; R275-E001, E002; R274-E008 | `HeaderInfo.source` receives the exact moved Arc allocation; header discovery returns normally. This only supplies the pointer-equality constructor premise, not parser acceptance. |
| Public `parse_file(source, header, syntax)` entry | Same-Arc assertion; effective operator selection; `cursor::parse_root` | R274-E009 | `Arc::ptr_eq` holds; operator table construction succeeds; parser returns the required CST without recovery. The source view shows the guard and calls, but fixture-specific success is unproved. |
| `cursor::discover_header` | `header::discover_header_with_cursor` using `Recover`, `GreenNodeBuilder`, and syntax cursor | R274-E003, E008; R274-E016 | Header loop terminates with the required discovery result and no recovery relevant to this fixture. |
| Header discovery callsite for each next item | `declaration::next_use_item_lex` re-exported by `declaration/mod.rs` | R274-E008; R275-E003, E004 | The forwarded cursor is valid and the item transaction returns. The excerpt shows two header callsites, including selector scanning; exact branch choices remain to be established. |
| `next_use_item_lex` | `current_item(..., |lex| scan_use_payload(lex))`; updates item offset and line entry | R275-E004, E005, E006, E007 | `current_item` returns `Some`; its token transaction commits; payload scanner classifies the token run as the intended item. `expect("Use scanning is total")` is a panic boundary, not evidence of success. |
| Root parser call | `parse_root` → root-statement sequence and item/parser owners | R274-E003, E009, E010, E012, E013, E014, E015 | The exact tokens produce the required CST, all parser transactions make the intended branches, and no recovery branch contributes. |
| HIR source lowering entry | `lower_module_with_local_source` → `lower_module_with_counters` | R274-E023; R275 view around R274-E023; R274-E001 fixture datum | The entry is available under the active `shadow` feature or test configuration; identity/import guards pass; lowering returns `Ok` with the exact root and fourteen-slot carrier. The fixture excerpt's test caller is not evidence for the function body. |
| Candidate collection entry | `Collection::collect` → candidate-mode/scoped/world constructors | R274-E024, E025 | Nonempty HIR world, all collection guards and allocations succeed; exact source carrier is retained; collection returns `Ok`. |
| Candidate source schedule and static-SCC entry | `emit_candidate_source` and the pinned candidate-source schedule / graph owners | R274-E025 plus inherited R274 excerpts for graph and SCC owners | Source schedule reaches the intended SCC operation and all guards/finite work succeed. The mere presence of schedule or SCC fields does not establish entry. |

## Coverage disposition

The two R274 omissions named in its stop receipt are now represented: the public
`scan_header` Arc-forwarder and the `next_use_item_lex` owner plus its
`current_item` and payload scanner. The compact route audit above covers the
visible header, parser, HIR, collection, and candidate/SCC constructors in the
inherited R274 view. It does not claim that every fixture-specific branch or
normal-return condition is satisfied. Sol's 300-second readiness pass must
check table-to-view correspondence, call-site forwarding and whether any
visible active owner on this fixed spine is still omitted. If an owner is
missing, record its exact callsite and stop before the main trial.
