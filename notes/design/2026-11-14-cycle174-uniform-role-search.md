# Uniform finite certificate search (planned types)

Role-DAG certification can remove caller-supplied fuel without changing the
language. List every declared parent and child role, allowing duplicates.
Given any decreasing rank, compress it by counting list entries strictly below
its value. Every child is in the list; its presence makes the compressed rank
strictly decrease along an edge. The compressed rank is at most list length.
Feed this rank into the already proved sufficient-fuel completeness theorem.

Target: `check registry (roleNodes registry).length = true` iff there exists
any RoleStratified rank. This decides only the syntactic role-DAG fragment,
not the accepted Yulang declaration language. Successful check can feed the
existing checked Exact theorem; false is not a language rejection. The list
may have duplicate roles, making the bound conservative but still finite.
