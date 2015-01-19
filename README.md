Sheafification
==============

Sheafification functor in type theory.

# Usage #
These files compile with the HoTT library https://github.com/HoTT/HoTT, commit 82f986cd7d4c17e70bba29e2f838dab07f8c2c85.

One can use the library with
```
/path/to/coq_makefile -R . "" *.v -o Makefile COQC = /path/to/hoqc  COQDEP = /path/to/hoqdep
```
then simply compiling with `make` (this can take some time, in particular `sheaf_induction.v`).

# Files #
`Utf8_core.v` contains notations

`cech_nerve.v` formalizes the notions of p-pullbacks, and Cech nerves

`cloture_hpullback.v`	formalizes the cloture of p-pullbacks

`colimit.v` contains definition of general colimits

`epi_mono.v` contains usual equivalences of epi and mono

`equivalence.v` contains some lemmas

`lemmas.v` contains some lemmas

`modalities.v` formalizes the notion of left exact modality

`nat_lemmas.v` contains some lemmas about nat

`reflective_subuniverse.v` formalizes the notion of reflective subuniverse

`sheaf_base_case.v` formalizes the not not modality on HProp

`sheaf_def_and_thm.v` gives definition of separated types and sheaves, as well as some properties about these objects

`sheaf_induction.v` formalizes the induction step

`sub_object_classifier.v` contains lemmas about subobject classifiers

`univalence.v` contains some lemmas
