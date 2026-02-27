# Yet another constructivisation of classical logic

The main completed part of the project is contained in the yac folder (yet another constructivisation).

It contains
* formula.ml ... definition of the raw syntax of terms and formulas and definition of substitution
* deduction.ml ... definition of the raw syntax of derivations
* properties.ml ... a witness extraction algorithm for cut-free derivations of geometric formulas and a cut elimination algorithm
* dickson.ml ... a classical derivation of the minimum principle and a derivation of a simple form of Dickson's lemma that follows from it
* print.ml ... pretty printing of formulas

In the main.ml file, I define an example ocaml function and run it through the pipeline of Dickson's lemma, cut elimination, witness extraction and pretty printing of the resulting witness.
