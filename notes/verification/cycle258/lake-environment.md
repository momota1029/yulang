I51 standalone checks use `cd lean && lake env lean --trust=0 -DwarningAsError=true Audit/Cycle258<Kind>.lean`.
First Usage attempt failed because lake replaced LEAN_PATH and the new module
was not yet in its build directory. No audit import was missing or added.
The verified focused cache outputs were linked into lake's normal build directory,
then all six independent invocations exited0. No lakefile or source setting changed.
Final rerun uses the fresh critical dependency outputs and the last new module.
