# BiLSK

## Compiling

Install K: https://github.com/kframework/k/releases

In the directory where `bils.k` is, run: `kompile --backend java bils.k`

## Usage

Files in our language may define two bounds at the top:

- `call-bound` bounds the total number of calls that may be made along a path
- `context-bound` bounds the total number of calls the context may make along a path

Use `krun` to check a file for bounded-equivalence.

Calling `krun` directly on a file returns the final configuration of a single random path.
e.g.
```
krun test_programs/ex2v1-e2.bils
```

To exhaustively check all paths up to the bound, use the `--search` option.
e.g. the following returns all final configurations reachable:
```
krun test_programs/ex2v1-e2.bils
```

We can filter paths found using the `--pattern` option.
e.g. the following returns all final configurations reachable where the mode is `_ERROR_` and prints the traces for said configurations as `T1` and `T2`:
```
krun --search --pattern "<mode> _ERROR_ </mode> <trace> T1 </trace> <trace> T2 </trace>" test_programs/ex2v1-e2.bils
```
