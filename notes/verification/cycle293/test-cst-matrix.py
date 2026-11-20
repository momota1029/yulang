"""Independent finite role-shape matrix; not Yulang parser acceptance."""
import json
from pathlib import Path
import subprocess
import tempfile

here=Path(__file__).resolve().parent
repo=here.parents[2]
fixture=(here/"documented-cst.json").read_text()
cases=[]
for pub in (False,True):
    for trivia in range(3):
        for form in ("required","binder","named","missing","noEq","extraMember","wrongHead"):
            root=json.loads(fixture)
            role=root[2][0]
            if not pub:
                role[2]=role[2][2:]
            r,b,c=(0,6 if pub else 4,0)
            if trivia==1:
                root[2].insert(0,["token","Whitespace"," "])
                r=1
                role[2].insert(b-1,["token","Whitespace"," "])
                b+=1
            sub=role[2][b][2][1][2]
            if trivia==2:
                sub.insert(0,["token","Whitespace"," "])
                c=1
            decl=sub[c][2]
            if form in ("binder","named","missing","noEq"):
                if form!="noEq":
                    decl.append(["token","Equals","="])
                rhs={
                    "binder":["token","SigilIdentifier","'key"],
                    "named":["token","Identifier","char"],
                    "missing":["node","Missing",[]],
                    "noEq":["token","Identifier","char"]
                }[form]
                decl.append(["node","TypeExpression",[rhs]])
            elif form=="extraMember":
                sub.append(["node","TypeDeclaration",decl[:]])
            elif form=="wrongHead":
                next(x for x in role[2] if x[1]=="TypeExpression")[2][1][2][-1]=[
                    "token","SigilIdentifier","'container"]
            predicted=[r,b,1,c] if form in ("required","binder","named") else None
            cases.append([root,[r],predicted])
with tempfile.TemporaryDirectory() as scratch:
    batch=Path(scratch)/"matrix.json"
    batch.write_text(json.dumps(cases,ensure_ascii=False))
    out=subprocess.run(["lake","env","lean","--trust=0","-DwarningAsError=true","--run",
        str(here/"run-cst-matrix.lean"),str(batch)],cwd=repo/"lean",capture_output=True,text=True,timeout=100)
    assert out.returncode==0,(out.returncode,out.stderr)
    assert out.stdout.strip()=="All 42 synthetic matrix cases matched",out.stdout
    print(out.stdout.strip())
