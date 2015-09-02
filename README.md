Sheafification
==============

Sheafification functor in type theory.

Compared with the version described in the paper, all problems mentionned in the first paragraph of section VI-B of the paper have been solved (the technical facts to show that ☐ is a modality are now proved, as well as the previously admitted lemmas about projections and collimits).

# Usage #
These files compile with the HoTT library https://github.com/HoTT/HoTT, commit 52852036cd371c1433bd211071da538d1cd2c6f4.

One can use the library with
```
/path/to/coq_makefile -f _CoqProject -o Makefile
```
with adapted modification in _CoqProject, 
then simply compiling with `make` (this can take some time).
