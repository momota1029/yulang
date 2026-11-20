"""Read exact Rust source checks for the two diagnostic boundaries (not Rust execution)."""
from pathlib import Path
import subprocess
repo=Path(__file__).resolve().parents[3]
base=next(ref for ref in ("adf9fae11d8e29273a28751089db2499bcf205d2",
                         "6972cc6221bb238ee79a96d3f868e25cda6b931c")
          if subprocess.run(["git","cat-file","-e",ref+"^{commit}"],cwd=repo,
                            stderr=subprocess.DEVNULL).returncode==0)
targets={
 "crates/yu-syntax/src/full_parse.rs":[
  "fn collect_syntax_diagnostics(",
  "if let Some((conflict, matches)) = conflicts.borrow_mut().get_mut(&range)",
  "SyntaxDiagnostic::conflicting_operator_fixity(",
  "SyntaxDiagnostic::structural(occurrence)",
  "fn parse_file_keeps_the_first_local_fixity_and_reports_the_rejected_site()",
  "operator construction must not masquerade as CST recovery",
  "SyntaxDiagnosticCause::ConflictingOperatorFixity(conflict) = diagnostic.cause()",
  "fn parse_file_emits_construction_and_recovery_in_cst_preorder()"],
 "crates/yu-syntax/src/structural_diagnostic.rs":[
  "children: node.children_with_tokens().collect(),",
  "occurrence_path.push(index as u32);",
  "fn flush(",
  "if let Some((range, index)) = run.take() {"],
 "crates/yu-syntax/src/tests/declaration/act_decl/operation_where.rs":[
  "fn role_method_signature_where_keeps_its_pre_wp17_recovery_cst()",
  "Error@49..50", "Error@50..51", "Error@51..58",
  "assert_eq!(parsed.structural_recoveries().len(), 1);",
  "assert_eq!(parsed.structural_recoveries()[0].range(), &(49..58));"],
}
for name, anchors in targets.items():
    p=repo/name
    current=p.read_bytes()
    fixed=subprocess.check_output(["git","show",f"{base}:{name}"],cwd=repo)
    assert current==fixed,name
    sha=subprocess.check_output(["git","rev-parse",f"{base}:{name}"],cwd=repo,text=True).strip()
    print(f"{name} exact blob {sha}")
    lines=current.decode().splitlines()
    for a in anchors:
        hits=[i for i,l in enumerate(lines,1) if a in l]
        assert hits,(name,a)
        print(f"  {','.join(map(str,hits))}: {a}")
print("Recorded golden: three raw Error tokens, one recorded structural recovery 49..58")
print("Operator diagnostics constructed separately; this is source inspection, not a Rust run.")
