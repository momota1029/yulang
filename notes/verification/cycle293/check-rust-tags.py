"""Check the wire vocabulary against the tracked Rust enum, without running Rust."""
import re
from pathlib import Path
import subprocess

repo = Path(__file__).resolve().parents[3]
rust = repo/"crates/yu-syntax/src/syntax_kind.rs"
lean = repo/"lean/Yulang/GeneralSourceRoleCstWireTags293.lean"
source = rust.read_text().split("pub enum SyntaxKind {",1)[1].split("\n}",1)[0]
labels = re.findall(r"^    ([A-Za-z][A-Za-z0-9]*)(?:\s*=\s*\d+)?,\s*$",source,re.M)
cases = lean.read_text().split("def labels",1)[1].split("def compact",1)[0]
frozen = re.findall(r'"([A-Za-z][A-Za-z0-9]*)"',cases)
assert labels == frozen and len(labels)==len(set(labels))==297
s = subprocess.check_output(["git","hash-object",str(rust)],text=True,cwd=repo).strip()
print("Rust enum exact lexical order:",len(labels),"known tags; source blob",s)
