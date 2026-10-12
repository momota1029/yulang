#!/usr/bin/env python3
"""Research-only, bounded explicit-state replay, not a compiler or proof oracle.

Run four fixed executions of native Lam/App/Let, constrain, extrude and
freshenAbove, with one candidate H and two named omissions. Every suspended
type operand is a cell index. Raw comparison keys and map/event identities
are historical tuples and deliberately outside H's active traversal.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


class Machine:
    """All persistent type references live in cells or row bound lists."""

    def __init__(self, mode, source):
        self.mode, self.source = mode, source
        self.cells, self.cell_roles, self.rows, self.envs = [], [], [], [{}]
        self.levels = ()  # Append-only immutable allocation levels, never union metadata.
        self.stack, self.caches, self.maps, self.events = [], [], [], []
        self.trace, self.publications, self.cuts, self.h_actions = [], [], [], []
        self.counts = Counter()
        self.result = self.cell(None, "final result")
        self.push("eval", term=source.term, env=0, lvl=0, owner=None, out=self.result)

    def run(self):
        while self.stack:
            self.counts["steps"] += 1
            assert self.counts["steps"] <= 1000, "finite step budget exceeded"
            self.step(self.stack.pop())
            self.check_levels()
        return self.report()

    def push(self, op, **kw):
        self.stack.append(dict(op=op, **kw))

    def cell(self, ty, role="temporary operand"):
        self.cells.append(ty)
        self.cell_roles.append(role)
        return len(self.cells) - 1

    def fresh(self, lvl, label):
        self.levels += (lvl,)
        self.rows.append(dict(level=lvl, label=label, lo=[], hi=[], retired=None))
        self.counts["allocations"] += 1
        return ("v", len(self.rows) - 1)

    def level(self, ty):
        return self.levels[ty[1]] if ty[0] == "v" else max(self.level(ty[1]), self.level(ty[2]))

    def environment(self, old, binder, body, lim=None):
        env = dict(self.envs[old])
        env[binder] = dict(body=body, lim=lim)
        self.envs.append(env)
        return len(self.envs) - 1

    def compare(self, left, right, owner, origin=None, receiver=None):
        cache = len(self.caches)
        self.caches.append(dict(owner=owner, keys=set()))
        self.push("constrain", left=left, right=right, cache=cache,
                  origin=origin, receiver=receiver)

    def recursive_compare(self, left, right, frame):
        self.push("constrain", left=left, right=right, cache=frame["cache"],
                  origin=frame["origin"], receiver=frame["receiver"])

    def step(self, f):
        op = f["op"]
        if op == "eval":
            t, env, lvl, out = f["term"], f["env"], f["lvl"], f["out"]
            if t[0] == "name":
                scheme = self.envs[env][t[1]]
                if scheme["lim"] is None:
                    self.cells[out] = self.cells[scheme["body"]]
                else:
                    memo = len(self.maps)
                    self.maps.append(dict(kind="freshen", lim=scheme["lim"], lvl=lvl, entries={}))
                    self.push("freshen", src=scheme["body"], out=out, memo=memo)
            elif t[0] == "lam":
                param = self.cell(self.fresh(lvl, self.source.labels[t[1]]), "Lam formal " + self.source.labels[t[1]])
                body = self.cell(None, "Lam body result")
                body_env = self.environment(env, t[1], param)
                self.push("lam_return", param=param, body=body, out=out)
                self.push("eval", term=t[2], env=body_env, lvl=lvl, owner=f["owner"], out=body)
            elif t[0] == "app":
                fun, arg = self.cell(None, "App callee"), self.cell(None, "App argument")
                self.push("app_arg", term=t, env=env, lvl=lvl, owner=f["owner"], fun=fun, arg=arg, out=out)
                self.push("eval", term=t[1], env=env, lvl=lvl, owner=f["owner"], out=fun)
            elif t[0] == "let":
                assert t[1], "only native recursive lets occur in fixed syntax"
                root = self.cell(self.fresh(lvl + 1, self.source.labels[t[2]]), "recursive root")
                body = self.cell(None, "let initializer result")
                rhs_env = self.environment(env, t[2], root)
                self.push("let_rhs_done", term=t, env=env, lvl=lvl, owner=f["owner"], root=root, body=body, out=out)
                self.push("eval", term=t[3], env=rhs_env, lvl=lvl + 1, owner=t[2], out=body)
            else:
                raise AssertionError(t)
        elif op == "lam_return":
            self.cells[f["out"]] = ("f", self.cells[f["param"]], self.cells[f["body"]])
        elif op == "app_arg":
            self.push("app_compare", **{k: v for k, v in f.items() if k != "op"})
            self.push("eval", term=f["term"][2], env=f["env"], lvl=f["lvl"], owner=f["owner"], out=f["arg"])
        elif op == "app_compare":
            result = self.cell(self.fresh(f["lvl"], "result@" + self.source.labels[f["term"][3]]), "App result")
            demand = self.cell(("f", self.cells[f["arg"]], self.cells[result]), "App demand")
            self.push("app_return", result=result, out=f["out"], value=f["term"][3])
            callee = f["term"][1]
            assert callee[0] == "name", "fixed-term receiver is direct resolved callee"
            self.compare(f["fun"], demand, "App " + self.source.labels[f["term"][3]], f["owner"], callee[1])
        elif op == "app_return":
            self.cells[f["out"]] = self.cells[f["result"]]
            self.cuts.append(dict(value=self.source.labels[f["value"]], store=self.store(),
                                  live=self.live(), caches=self.cache_report()))
        elif op == "let_rhs_done":
            self.push("let_publish", **{k: v for k, v in f.items() if k != "op"})
            self.compare(f["body"], f["root"], "completion " + self.source.labels[f["term"][2]])
        elif op == "let_publish":
            t = f["term"]
            self.publications.append(dict(binder=self.source.labels[t[2]], boundary=f["lvl"],
                                          root=self.show(self.cells[f["root"]]), initializer=self.show(self.cells[f["body"]])))
            env = self.environment(f["env"], t[2], f["root"], f["lvl"])
            self.push("eval", term=t[4], env=env, lvl=f["lvl"], owner=f["owner"], out=f["out"])
        elif op == "constrain":
            self.constrain(f)
        elif op == "constrain_return":
            self.recursive_compare(f["left"], f["right"], f)
        elif op in ("extrude", "freshen"):
            self.copy(f)
        elif op == "function_return":
            self.cells[f["out"]] = ("f", self.cells[f["arg"]], self.cells[f["res"]])
        elif op == "copy_bounds_return":
            target = self.rows[f["target"]]
            for side, slots in f["sides"].items():
                target[side] = [self.cells[s] for s in reversed(slots)] if f["kind"] == "freshen" else [self.cells[s] for s in slots]
            self.cells[f["out"]] = ("v", f["target"])
            if f["kind"] == "extrude":
                pair = dict(parent=f["parent"], copy=f["target"], polarity=f["pol"], level=target["level"])
                self.events[f["event"]]["pairs"].append(pair)
                if self.mode != "stock" and self.events[f["event"]]["qualified"]:
                    self.h(f["parent"], f["target"], f["event"])
        else:
            raise AssertionError(op)

    def constrain(self, f):
        lhs, rhs = self.cells[f["left"]], self.cells[f["right"]]
        self.counts["comparisons"] += 1
        if lhs[0] == rhs[0] == "v" and lhs == rhs:
            self.counts["identity_returns"] += 1
            return
        key = (lhs, rhs)
        cached = False
        if lhs[0] == "v" or rhs[0] == "v":
            keys = self.caches[f["cache"]]["keys"]
            cached = key in keys
            if not cached:
                keys.add(key)
        self.trace.append(dict(owner=self.caches[f["cache"]]["owner"], left=self.show(lhs), right=self.show(rhs), cached=cached))
        if cached:
            self.counts["cache_returns"] += 1
            return
        if lhs[0] == rhs[0] == "f":
            self.recursive_compare(self.cell(lhs[2]), self.cell(rhs[2]), f)
            self.recursive_compare(self.cell(rhs[1]), self.cell(lhs[1]), f)
        elif lhs[0] == "v" and self.level(rhs) <= self.level(lhs):
            row = self.rows[lhs[1]]
            row["hi"].insert(0, rhs)
            self.counts["upper_insertions"] += 1
            for bound in reversed(row["lo"]):
                self.recursive_compare(self.cell(bound), f["right"], f)
        elif rhs[0] == "v" and self.level(lhs) <= self.level(rhs):
            row = self.rows[rhs[1]]
            row["lo"].insert(0, lhs)
            self.counts["lower_insertions"] += 1
            for bound in reversed(row["hi"]):
                self.recursive_compare(f["left"], self.cell(bound), f)
        else:
            assert lhs[0] == "v" or rhs[0] == "v"
            positive = rhs[0] == "v"
            level = self.level(rhs if positive else lhs)
            event, memo = len(self.events), len(self.maps)
            qualified = f["origin"] is not None and self.source.same_scc(f["origin"], f["receiver"])
            self.events.append(dict(origin=f["origin"], receiver=f["receiver"], qualified=qualified, pairs=[]))
            self.maps.append(dict(kind="extrude", lvl=level, entries={}, event=event))
            result = self.cell(None, "extruded return")
            self.push("constrain_return", left=result if positive else f["left"], right=f["right"] if positive else result,
                      cache=f["cache"], origin=f["origin"], receiver=f["receiver"])
            self.push("extrude", src=f["left"] if positive else f["right"], out=result, memo=memo, pol=positive)

    def copy(self, f):
        kind, ty, memo = f["op"], self.cells[f["src"]], self.maps[f["memo"]]
        limit = memo["lim"] if kind == "freshen" else memo["lvl"]
        if self.level(ty) <= limit:
            self.cells[f["out"]] = ty
            self.counts[kind + "_retained"] += 1
            return
        if ty[0] == "f":
            arg, res = self.cell(None), self.cell(None)
            self.push("function_return", arg=arg, res=res, out=f["out"])
            for child, dst, pol in [(ty[2], res, f.get("pol")), (ty[1], arg, not f.get("pol", False))]:
                kw = dict(src=self.cell(child), out=dst, memo=f["memo"])
                if kind == "extrude":
                    kw["pol"] = pol
                self.push(kind, **kw)
            return
        assert ty[0] == "v"
        parent = ty[1]
        key = (parent, f["pol"]) if kind == "extrude" else parent
        if key in memo["entries"]:
            self.cells[f["out"]] = ("v", memo["entries"][key])
            self.counts[kind + "_memo_hits"] += 1
            return
        target_ty = self.fresh(memo["lvl"], self.rows[parent]["label"] + ("+copy" if f.get("pol") else "-copy") if kind == "extrude" else self.rows[parent]["label"] + "@use" + str(f["memo"]))
        target = target_ty[1]
        memo["entries"][key] = target
        if kind == "extrude":
            side, direct = ("lo", "hi") if f["pol"] else ("hi", "lo")
            self.rows[parent][direct].insert(0, target_ty)
            sides = {side: list(self.rows[parent][side])}
        else:
            sides = {side: list(reversed(self.rows[parent][side])) for side in ("lo", "hi")}
        slots = {side: [self.cell(None) for _ in bounds] for side, bounds in sides.items()}
        self.push("copy_bounds_return", kind=kind, target=target, parent=parent, sides=slots,
                  out=f["out"], event=memo.get("event"), pol=f.get("pol"))
        # Stack reversal preserves Scala lower-then-upper and oldest-first freshening.
        children = [(bound, dst) for side, bounds in sides.items() for bound, dst in zip(bounds, slots[side])]
        for bound, dst in reversed(children):
            kw = dict(src=self.cell(bound), out=dst, memo=f["memo"])
            if kind == "extrude":
                kw["pol"] = f["pol"]
            self.push(kind, **kw)

    def h(self, parent, anchor, event):
        """Finite candidate: union both sides, transport live cells; no supplied store."""
        before = self.live()
        before_cells = list(self.cells)
        old_levels = [r["level"] for r in self.rows]
        allocation_levels = self.levels
        old_keys = [set(c["keys"]) for c in self.caches]
        old_maps = [dict(m["entries"]) for m in self.maps]

        def q(ty):
            if ty is None:
                return None
            if ty[0] == "v":
                return ("v", anchor) if ty[1] == parent else ty
            return ("f", q(ty[1]), q(ty[2]))

        for side in ("lo", "hi"):
            self.rows[anchor][side] += self.rows[parent][side]
            self.rows[parent][side] = []
        self.rows[parent]["retired"] = anchor
        for row in self.rows:
            for side in ("lo", "hi"):
                row[side] = [q(ty) for ty in row[side]]
        # Environment and all continuation fields refer to these cell indices.
        if self.mode != "bounds_only":
            self.cells[:] = [q(ty) for ty in self.cells]
        if self.mode == "canonical_cache":
            for cache in self.caches:
                cache["keys"] = {(q(left), q(right)) for left, right in cache["keys"]}
        else:
            assert old_keys == [c["keys"] for c in self.caches]
        assert old_maps == [m["entries"] for m in self.maps]
        assert old_levels == [r["level"] for r in self.rows]
        assert self.levels is allocation_levels
        assert not self.rows[anchor]["lo"] or not self.rows[anchor]["hi"], "this bounded union has no cross products"
        self.counts["H_actions"] += 1
        changed = [i for i, (old, new) in enumerate(zip(before_cells, self.cells)) if old != new]
        if self.mode != "bounds_only":
            assert all(q(ty) == ty for ty in self.cells)
        assert all(q(ty) == ty for row in self.rows for side in ("lo", "hi") for ty in row[side])
        self.h_actions.append(dict(parent=parent, anchor=anchor, event=event,
                                   before=before, after=self.live(), historical_keys=self.cache_report(),
                                   changed_cells=changed, allocation_levels=list(self.levels),
                                   suspended_frames=[dict(frame) for frame in self.stack],
                                   environments=[{str(b): dict(s) for b, s in env.items()} for env in self.envs]))

    def check_levels(self):
        for i, row in enumerate(self.rows):
            assert row["level"] == self.levels[i]
            for side in ("lo", "hi"):
                assert all(self.level(ty) <= row["level"] for ty in row[side]), "bound-level invariant"

    def show(self, ty):
        if ty is None:
            return "pending"
        if ty[0] == "v":
            return self.rows[ty[1]]["label"] + "#" + str(ty[1])
        return "F(" + self.show(ty[1]) + "," + self.show(ty[2]) + ")"

    def store(self):
        return [dict(id=i, label=r["label"], level=r["level"], retired=r["retired"],
                     lower=[self.show(t) for t in r["lo"]], upper=[self.show(t) for t in r["hi"]]) for i, r in enumerate(self.rows)]

    def live(self):
        return [dict(cell=i, role=role, type=self.show(ty)) for i, (ty, role) in enumerate(zip(self.cells, self.cell_roles))
                if role.startswith(("Lam formal", "App result", "App demand"))]

    def cache_report(self):
        return [dict(owner=c["owner"], keys=sorted([self.show(l) + " <: " + self.show(r) for l, r in c["keys"]])) for c in self.caches]

    def report(self):
        maps = []
        for m in self.maps:
            entries = []
            for key, value in m["entries"].items():
                parent, pol = key if isinstance(key, tuple) else (key, None)
                entries.append(dict(parent=parent, polarity=pol, copy=value))
            maps.append(dict(**{k: v for k, v in m.items() if k != "entries"}, entries=entries))
        return dict(mode=self.mode, counts=dict(self.counts), result=self.show(self.cells[self.result]),
                    store=self.store(), maps=maps, events=self.events, publications=self.publications,
                    cuts=self.cuts, H=self.h_actions, comparisons=self.trace, caches=self.cache_report(),
                    compact=self.compact_interface())

    def compact_interface(self):
        """Reference canonicalize subset for these variable/function-only runs.

        Refuse recursive compact layers or a variable occurring in both polarities;
        this is not the general TypeSimplifier. Closure walks actual computed bounds.
        """
        def empty():
            return dict(vars=set(), fun=None)

        def merge(a, b):
            fun = a["fun"] or b["fun"]
            if a["fun"] and b["fun"]:
                fun = (merge(a["fun"][0], b["fun"][0]), merge(a["fun"][1], b["fun"][1]))
            return dict(vars=a["vars"] | b["vars"], fun=fun)

        def go0(ty, pol):
            if ty[0] == "f":
                return dict(vars=set(), fun=(go0(ty[1], not pol), go0(ty[2], pol)))
            visited, todo = set(), [ty[1]]
            while todo:
                row = todo.pop()
                if row not in visited:
                    visited.add(row)
                    todo.extend(t[1] for t in self.rows[row]["lo" if pol else "hi"] if t[0] == "v")
            return dict(vars=visited, fun=None)

        def key(ct):
            return (tuple(sorted(ct["vars"])), None if ct["fun"] is None else tuple(key(c) for c in ct["fun"]))

        def go1(ct, pol, active):
            signature = (key(ct), pol)
            assert signature not in active, "recursive compact layer outside bounded simplifier"
            bound = empty()
            for row in sorted(ct["vars"]):
                for ty in self.rows[row]["lo" if pol else "hi"]:
                    if ty[0] != "v":
                        bound = merge(bound, go0(ty, pol))
            result = merge(ct, bound)
            if result["fun"]:
                result["fun"] = (go1(result["fun"][0], not pol, active | {signature}),
                                 go1(result["fun"][1], pol, active | {signature}))
            return result

        compact = go1(go0(self.cells[self.result], True), True, set())
        occurrences = {}

        def occurrence(ct, pol):
            for row in ct["vars"]:
                occurrences.setdefault(row, set()).add(pol)
            if ct["fun"]:
                occurrence(ct["fun"][0], not pol)
                occurrence(ct["fun"][1], pol)
        occurrence(compact, True)
        assert all(len(pols) == 1 for pols in occurrences.values()), "general co-occurrence simplifier not implemented"

        def dump(ct):
            return dict(vars=sorted(ct["vars"]), fun=None if not ct["fun"] else [dump(c) for c in ct["fun"]])

        def display(ct, pol):
            # All variables here were verified nonrecursive and single-polarity.
            return "Top" if not ct["fun"] and not pol else "Bot" if not ct["fun"] else "(" + display(ct["fun"][0], not pol) + " -> " + display(ct["fun"][1], pol) + ")"
        return dict(canonical=dump(compact), recursive_variables=[],
                    polarities={str(v): list(p) for v, p in occurrences.items()}, simplified=display(compact, True))


class Source:
    """Resolve native syntax first; derive source-only incidences, never type edges."""

    def __init__(self):
        raw = ("let", True, "odd", ("lam", "n_outer", ("let", True, "even",
               ("lam", "n_inner", ("app", ("name", "odd"), ("name", "n_inner"))),
               ("app", ("name", "even"), ("name", "n_outer")))), ("name", "odd"))
        self.labels, self.edges = {}, {}
        self.term = self.resolve(raw, {})
        self.walk(self.term, None)

    def binder(self, label):
        idx = len(self.labels)
        self.labels[idx] = label
        self.edges[idx] = set()
        return idx

    def resolve(self, t, env):
        if t[0] == "name":
            return ("name", env[t[1]])
        if t[0] == "lam":
            binder = self.binder(t[1])
            return ("lam", binder, self.resolve(t[2], dict(env, **{t[1]: binder})))
        if t[0] == "let":
            binder = self.binder(t[2])
            inside = dict(env, **{t[2]: binder})
            return ("let", t[1], binder, self.resolve(t[3], inside), self.resolve(t[4], inside))
        assert t[0] == "app"
        fun, arg = self.resolve(t[1], env), self.resolve(t[2], env)
        return ("app", fun, arg, self.binder("apply" + str(len(self.labels))))

    def fragment_names(self, t):
        if t[0] == "name":
            return {t[1]}
        assert t[0] == "app", "unsettled fragment boundaries excluded from this term"
        return self.fragment_names(t[1]) | self.fragment_names(t[2])

    def walk(self, t, owner):
        if t[0] == "name":
            if owner is not None:
                self.edges[owner].add(t[1])
        elif t[0] == "lam":
            self.walk(t[2], owner)
        elif t[0] == "let":
            self.walk(t[3], t[2])
            self.walk(t[4], owner)
        else:
            self.edges[t[3]].update(self.fragment_names(t))
            self.walk(t[1], owner)
            self.walk(t[2], owner)

    def reach(self, start):
        visited, todo = set(), [start]
        while todo:
            vertex = todo.pop()
            if vertex not in visited:
                visited.add(vertex)
                todo.extend(self.edges[vertex])
        return visited

    def same_scc(self, left, right):
        return right in self.reach(left) and left in self.reach(right)

    def report(self):
        return dict(resolved_term=self.term, labels=self.labels,
                    edges={self.labels[v]: sorted(self.labels[w] for w in ws) for v, ws in self.edges.items()},
                    components={self.labels[v]: sorted(self.labels[w] for w in self.edges if self.same_scc(v, w)) for v in self.edges})


def check_discriminators(runs):
    stock, h, bounds, cache = runs
    assert len(stock["H"]) == 0 and len(h["H"]) == 2
    assert [(p["parent"], p["copy"], p["polarity"]) for p in h["events"][0]["pairs"]] == [(3, 5, True), (4, 6, False)]
    assert [(r["id"], r["level"], r["retired"]) for r in h["store"] if r["id"] in (3, 4, 5, 6)] == [(3, 2, 5), (4, 2, 6), (5, 1, None), (6, 1, None)]
    assert [len(m["entries"]) for m in h["maps"] if m["kind"] == "freshen"] == [1, 5]
    assert [len(m["entries"]) for m in stock["maps"] if m["kind"] == "freshen"] == [3, 6]
    assert [len(m["entries"]) for m in bounds["maps"] if m["kind"] == "freshen"] == [3, 6]
    assert h["publications"][0]["initializer"].startswith("F(n_inner+copy#5,result@apply4-copy#6)")
    assert bounds["publications"][0]["initializer"].startswith("F(n_inner#3,result@apply4#4)")
    assert h["cuts"][0]["store"][0]["upper"] == ["F(n_inner+copy#5,result@apply4-copy#6)"]
    assert cache["cuts"][0]["store"][0]["upper"] == []
    assert cache["comparisons"][1]["cached"] is True
    assert h["comparisons"][1]["cached"] is False
    assert len(h["cuts"][0]["caches"][0]["keys"]) == 2
    assert any(c["role"] == "Lam formal n_inner" and c["type"] == "n_inner+copy#5" for c in h["H"][0]["after"])
    assert any(c["role"] == "App result" and c["type"] == "result@apply4-copy#6" for c in h["H"][1]["after"])
    assert all(not action["changed_cells"] for action in bounds["H"])
    assert [p["boundary"] for p in h["publications"]] == [1, 0]
    assert h["compact"]["canonical"] == dict(vars=[9], fun=[dict(vars=[10, 11], fun=None), dict(vars=[12], fun=None)])
    assert all(r["compact"]["simplified"] == "(Top -> Bot)" for r in runs)
    return dict(status="all bounded discriminators passed", executions=4,
                covered="one resolved term; no independent semantic oracle or arbitrary histories")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="optional scratch report path")
    args = parser.parse_args()
    source = Source()
    runs = [Machine(mode, source).run() for mode in ("stock", "H", "bounds_only", "canonical_cache")]
    checks = check_discriminators(runs)
    root = Path(__file__).resolve().parents[1]
    inputs = ["reference/Typer.scala", "reference/TypeSimplifier.scala",
              "notes/theory/2026-10-12-fixed-term-intrusion-quotient-proof.md",
              "notes/design/2026-10-11-yulang-inference-top-level-principles.md",
              "notes/design/2026-10-10-parent-copy-scc-intrusion.md",
              "notes/design/2026-10-12-intrusion-value-type-association.md",
              "notes/design/2026-10-12-value-reference-copied-row-ownership.md"]
    dependencies = {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in inputs if (root / p).exists()}
    reference_hashes = {inputs[0]: "f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9",
                        inputs[1]: "618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b"}
    for p, expected in reference_hashes.items():
        if p in dependencies:
            assert dependencies[p] == expected
    dependencies.update(reference_hashes)
    report = dict(status="unreviewed research evidence", checks=checks, source=source.report(), dependencies=dependencies, runs=runs)
    if args.json:
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(checks=checks, source=source.report(), runs=[dict(mode=r["mode"], counts=r["counts"],
                     publications=r["publications"], maps=r["maps"], store=r["store"], compact=r["compact"]) for r in runs]), indent=2))


if __name__ == "__main__":
    main()
