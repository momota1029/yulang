"""Exercise the real Lean CLI on a documented CST mirror, not on Yulang source."""
import json
from pathlib import Path
import subprocess
import tempfile

repo = Path(__file__).resolve().parents[3]
driver = Path(__file__).with_name("run-unresolved-cst.lean").resolve()
reference = Path(__file__).with_name("documented-cst.json").read_text()
orig = json.loads(reference)
def copy():
    return json.loads(reference)
def withMember(rhs):
    x=copy()
    body=x[2][0][2][6][2]
    body[1][2][0][2] += [["token","Whitespace"," "],["token","Equals","="],
                        ["token","Whitespace"," "],rhs]
    return x

with tempfile.TemporaryDirectory() as tmp:
    def cli(data, path):
        p = Path(tmp)/"input.json"
        p.write_text(data if isinstance(data,str) else json.dumps(data,ensure_ascii=False))
        return subprocess.run(
            ["lake","env","lean","--trust=0","-DwarningAsError=true","--run",
             str(driver),str(p),*path],cwd=repo/"lean",capture_output=True,text=True,timeout=100)
    expected={"role":"Index","path":[0],"binders":["'container","'key"],
              "directMembers":[{"body":"required","name":"value","path":[0,6,1,0]},
                               {"kind":"nonType","path":[0,6,3,0]}]}
    r=cli(orig,["0"])
    assert r.returncode==0 and json.loads(r.stdout)==expected,(r.returncode,r.stderr,r.stdout)
    print("documented unresolved role:",r.stdout.strip())
    for kind,val,tag in [("Identifier","char","unresolvedName"),("SigilIdentifier","'key","binder")]:
        r=cli(withMember(["node","TypeExpression",[["token",kind,val]]]),["0"])
        assert r.returncode==0,(r.returncode,r.stderr)
        got=json.loads(r.stdout)
        assert got["directMembers"][0]["body"]==[tag,val],got
        assert got["directMembers"][0]["path"]==[0,6,1,0],got
        print(f"exact named/positional RHS {val!r}:",r.stdout.strip())
    r=cli(withMember(["node","TypeExpression",[["node","Missing",[]]]]),["0"])
    assert r.returncode==1 and "foreignOrUnsupportedRole" in r.stderr,(r.returncode,r.stderr)
    print("recovered RHS fails; not a required member")
    x=copy()
    x[2][0][2][6][2][3][2][0][2].append(["node","FakeRustKind",[]])
    r=cli(x,["0"])
    assert r.returncode==1 and "unknownTag" in r.stderr,(r.returncode,r.stderr)
    print("unknown nested tag fails")
    r=cli(orig,["1"])
    assert r.returncode==1 and "foreignOrUnsupportedRole" in r.stderr,(r.returncode,r.stderr)
    print("wrong mixed child path fails")
    r=cli(["node","Root",[],"extra"],["0"])
    assert r.returncode==1 and "schemaOrDepth" in r.stderr,(r.returncode,r.stderr)
    print("extra JSON field fails")
    r=cli("{badJson",["0"])
    assert r.returncode==1 and ".json" in r.stderr,(r.returncode,r.stderr)
    print("malformed JSON fails")
