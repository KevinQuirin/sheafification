Sheafification
==============

Sheafification functor in type theory.

Compared with the version described in the paper, all problems mentionned in the first paragraph of section VI-B of the paper has been solved (the technical facts to show that ☐ is a modality are now proved, as well as the previously admitted lemmas about projections and collimits).

# Usage #
These files compile with the HoTT library https://github.com/HoTT/HoTT, commit 247016b019c48e761b58751bafa71ef22ee4edaf.

One can use the library with
```
/path/to/coq_makefile -R . "" *.v -o Makefile COQC = /path/to/hoqc  COQDEP = /path/to/hoqdep
```
then simply compiling with `make` (this can take some time, in particular `sheaf_induction.v` (approximatively 10 minutes on my computer).

# Files #
`Utf8_core.v` contains notations.

`cech_nerve.v` formalizes the notions of p-pullbacks, and Cech nerves.

  ↳ Definition 7, 8, 9
  
`cloture_hpullback.v`	formalizes the cloture of p-pullbacks.

`colimit.v` contains definition of general colimits.

  ↳ Definitions 5, 6
  
`epi_mono.v` contains usual equivalences of epi and mono.

  ↳ Definition 3
  
`equivalence.v` contains some lemmas.

`lemmas.v` contains some lemmas.

`modalities.v` formalizes the notion of left exact modality.

  ↳ Definition 10 (v), Proposition 12
  
`nat_lemmas.v` contains some lemmas about nat.

`reflective_subuniverse.v` formalizes the notion of reflective subuniverse.

  ↳ Definition 10 ((i) to (iv)), Proposition 11, Lemma 13, 14, 15
  
`sheaf_base_case.v` formalizes the not not modality on HProp.

`sheaf_def_and_thm.v` gives definition of separated types and sheaves, as well as some properties about these objects.

  ↳ Definition 18, 19, 20, 21, 22, Proposition 23, 24, 25
  
`sheaf_induction.v` formalizes the induction step.

  ↳ Proposition 26, 27, Lemma 28, 29, Proposition 30, 31, Lemma 32, Proposition 33, 34, 36
  
`sub_object_classifier.v` contains lemmas about subobject classifiers.

`univalence.v` contains some lemmas.
