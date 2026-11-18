"""Algorithm experiment only, not Lean evidence or Yulang runtime validation.
Compare finite undirected alias flood closure against an independent partition
implementation, exhaustively for four named vertices including isolated ones.
"""
from itertools import combinations
from collections import deque

def flood(edges, root, queries):
    universe=set(queries)|{root}|{v for edge in edges for v in edge}
    visited={root}; rounds=0
    while True:
        new=visited|{b for a,b in edges if a in visited}|{a for a,b in edges if b in visited}
        assert new <= universe and visited <= new
        if new==visited:
            assert all((a in visited)==(b in visited) for a,b in edges)
            return visited,rounds
        assert len(universe-new)<len(universe-visited)
        visited=new; rounds+=1
        assert rounds<=len(universe)-1

def partition(edges, root, queries):
    universe=set(queries)|{root}|{v for edge in edges for v in edge}
    parent={v:v for v in universe}
    def find(v):
        while parent[v]!=v:v=parent[v]
        return v
    for a,b in edges:parent[find(a)]=find(b)
    return {v for v in universe if find(v)==find(root)}

vertices=range(4); possible=list(combinations(vertices,2)); count=0; maximum=0
for mask in range(1<<len(possible)):
    edges=[edge for i,edge in enumerate(possible) if mask&(1<<i)]
    for root in range(5): # fifth root is isolated and absent from all edges
        seen,rounds=flood(edges,root,list(vertices)+[11])
        assert seen==partition(edges,root,list(vertices)+[11])
        assert (11 in seen)==(root==11)
        maximum=max(maximum,rounds);count+=1
# A chain through identities which are not query/site IDs must not be pruned.
assert flood([(3,7),(7,19)],3,[3,19])[0]=={3,7,19}
# Preserve original request multiplicity/order after deciding alias membership.
sites=[(3,[(0,10)]),(19,[(0,20),(0,20)]),(11,[(1,30)])]
component,_=flood([(3,7),(7,19)],3,[identity for identity,_ in sites])
requests=[output for identity,outputs in sites if identity in component for output in outputs]
assert requests==[(0,10),(0,20),(0,20)]
print(f'PROTOTYPE-PASS: {count} exhaustive graph/root cases; maximum growth rounds {maximum}; external-endpoint and duplicate/order regressions PASS')
print('Scope: Python algorithm experiment only; no Lean Alias equivalence or executable request compiler theorem yet.')
