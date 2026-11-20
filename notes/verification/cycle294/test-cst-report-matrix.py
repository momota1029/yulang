"""Compare Lean's archived CST report against an independent raw-path walk."""
import json
import os
import subprocess
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
repo = here.parents[2]
lean = repo / "lean"
report = here / "run-cst-mark-report.lean"
runner = os.environ.get("CST_MATRIX_LEAN", "lake env lean").split()
marks = {"Missing": "missing", "Invalid": "invalid", "Error": "error",
         "NestingTooDeep": "error", "Unknown": "error"}


def classified(path, focus):
    if path[:len(focus)] == focus:
        return "selected"
    if focus[:len(path)] == path:
        return "ancestor"
    return "unrelated"


def independent_wire_marks(wire, focus):
    out = []

    def walk(w, path, start):
        mode, label, inner = w
        if mode == "token":
            width = len(inner.encode())
        else:
            offset = start
            for i, c in enumerate(inner):
                offset += walk(c, path + [i], offset)
            width = offset - start
        if label in marks:
            out.append(dict(zone=classified(path, focus), path=path, kind=marks[label],
                            low=start, high=start + width))
        return width

    walk(wire, [], 0)
    return sorted(out, key=lambda x: x["path"])


def exec_report(f, focus):
    return subprocess.run(runner + ["--trust=0", "-M", "3200", "-DwarningAsError=true",
                                    "--run", str(report), str(f), *map(str, focus)], cwd=lean,
                          text=True, capture_output=True, timeout=40)


def check(file, focus, expected_role, selected_ok, whole_ok):
    p = exec_report(file, focus)
    assert p.returncode == 0, p.stderr
    result = json.loads(p.stdout)
    expected = independent_wire_marks(json.loads(file.read_text()), focus)
    assert result["wireMarks"] == expected, (result, expected)
    assert result["path"] == focus
    assert result["selectedBranchMarkFree"] == all(a["zone"] == "unrelated" for a in expected)
    assert result["wholeWireMarkFree"] == (len(expected) == 0)
    assert result["rustDiagnosticsChecked"] is False
    assert result["candidateRole"] == expected_role
    assert result["projectionAdmittedUnderWholeMarkPolicy"] is whole_ok
    assert result["projectionAdmittedUnderSelectedMarkPolicy"] is selected_ok


archived = here.parent / "cycle293" / "recorded-rust-cst.json"
rcst = json.loads(archived.read_text())
role = rcst[2][0]
check(archived, [0], "a", True, False)
check(archived, [], None, False, False)
check(archived, [999], None, False, False)

case = here / "recorded-case-missing.json"
nested = here / "recorded-for-error.json"
check(case, [0, 0, 1], None, False, False)
check(case, [0, 0, 2], None, False, False)
check(nested, [0, 0, 2], None, False, False)
check(nested, [0, 0, 9], None, False, False)

with tempfile.TemporaryDirectory(prefix="cst-wire-controls-") as temp:
    f = Path(temp) / "sample.json"

    def sample(wire):
        f.write_text(json.dumps(wire, ensure_ascii=False), encoding="utf8")
        return f

    check(sample(["node", "Root", [role]]), [0], "a", True, True)
    check(sample(["node", "Root", [["node", "Error", [role]]]]), [0, 0], "a", False, False)
    check(sample(["node", "Root", [["node", "NestingTooDeep", [role]]]]), [0, 0], "a", False, False)
    check(sample(["node", "Root", [role, ["token", "Identifier", "雪"],
                                  ["node", "Missing", []], ["token", "Unknown", ""]]]),
          [0], "a", True, False)
    check(sample(["node", "Root", [role, ["token", "Identifier", "雪"],
                                  ["node", "Missing", []], ["token", "Unknown", ""]]]),
          [2], None, False, False)
    # Malformed JSON and beyond-fuel depth are not statements of cleanliness.
    f.write_text('{"not":"an array"}')
    assert exec_report(f, [0]).returncode == 1
    f.write_text("{broken-json")
    assert exec_report(f, [0]).returncode == 1
    assert exec_report(sample(["node", "Root", [["token", "UnknownNewTag", "x"]]]), [0]).returncode == 1
    d = ["token", "Identifier", ""]
    for i in range(66):
        d = ["node", "Root", [d]]
    assert exec_report(sample(d), [0]).returncode == 1

print("12 archived/synthetic report controls match independent mixed-child traversal and UTF-8 spans.")
print("4 malformed/unknown/too-deep wire inputs rejected before producing any report.")
print("The matrix executes Lean only; separately supplied parser diagnostics are never marked checked.")
