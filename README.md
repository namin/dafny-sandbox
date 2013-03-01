Dafny for Metatheory of Programming Languages
=============================================

Dafny
-----

Dafny is an [open-source](http://dafny.codeplex.com/) automatic program
verifier for functional correctness developed at
[Microsoft Research](http://research.microsoft.com/en-us/projects/dafny/).

Software Foundations
--------------------

Software Foundations is a textbook on programming languages written in
[Coq](http://coq.inria.fr) and
[available online](http://www.cis.upenn.edu/~bcpierce/sf/).

I've translated some parts of Software Foundations from Coq to Dafny.

* [Imp](https://github.com/namin/dafny-sandbox/blob/master/Imp.dfy)
* [Types: Type Systems](https://github.com/namin/dafny-sandbox/blob/master/Imp.dfy)
* [Stlc: The Simply Typed Lambda-Calculus](https://github.com/namin/dafny-sandbox/blob/master/Stlc.dfy)
* [Norm: Normalization of STLC](https://github.com/namin/dafny-sandbox/blob/master/MoreStlc.dfy)
* [References: Typing Mutable References](https://github.com/namin/dafny-sandbox/blob/master/References.dfy)

Beyond Software Foundations
---------------------------

* [StlcLn: Locally-nameless STLC](https://github.com/namin/dafny-sandbox/blob/master/StlcLn.dfy):
  the locally-nameless representation with cofinite quantification works
  very well in Coq. However, I haven't found a translation in Dafny
  which is pleasant to work with (because of the cofinite
  quantification), so abandoning this attempt for now.

Step-Indexed Logical Relations
------------------------------

Step-indexed logical relations seem like a natural fit for Dafny. Hence,
I am formalizing
[Amal Ahmed's Lectures on Logical Relations](http://www.cs.uoregon.edu/Activities/summerschool/summer12/curriculum.html).

* [Lr_Ts_Stlc.dfy](https://github.com/namin/dafny-sandbox/blob/master/Lr_Ts_Stlc.dfy):
  Proof of type-safety of the STLC using step-indexed logical relations.

* [Lr_Ts_Stlc_IsoRecTypes.dfy](https://github.com/namin/dafny-sandbox/blob/master/Lr_Ts_Stlc_IsoRecTypes.dfy):
  Augment STLC with iso-recursive types (explicit `fold` and `unfold`).
  The previous proof simply needs to be augmented as well. The old cases remain unchanged.
