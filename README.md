Dafny for Metatheory of Programming Languages
=============================================

[Related talk at MSR](http://research.microsoft.com/apps/video/default.aspx?id=198423).

[Dafny](https://dafny.org/)
-----

Software Foundations
--------------------

Software Foundations is a textbook on programming languages written in
[Coq](http://coq.inria.fr) and
[available online](https://softwarefoundations.cis.upenn.edu/).

I've translated some parts of Software Foundations from Coq to Dafny.

* [Imp](https://github.com/namin/dafny-sandbox/blob/master/Imp.dfy)
* [Types: Type Systems](https://github.com/namin/dafny-sandbox/blob/master/Imp.dfy)
* [Stlc: The Simply Typed Lambda-Calculus](https://github.com/namin/dafny-sandbox/blob/master/Stlc.dfy)
* [Norm: Normalization of STLC](https://github.com/namin/dafny-sandbox/blob/master/Norm.dfy)
* [References: Typing Mutable References](https://github.com/namin/dafny-sandbox/blob/master/References.dfy)

Beyond Software Foundations
---------------------------

* [StlcLn: Locally-nameless STLC](https://github.com/namin/dafny-sandbox/blob/master/StlcLn.dfy)
* [LnSystemF: Locally-nameless System F](https://github.com/namin/dafny-sandbox/blob/master/LnSystemF.dfy)
* [DependentTypes: a syntax-directed dependently typed system](https://github.com/namin/dafny-sandbox/blob/master/DependentTypes.dfy)

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
