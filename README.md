# PMRSAbs

PMRSAbs is a Model Checker for Pattern Matching Recursion Schemes
and Alternating Trivial Automata (ATT). It uses [Preface](http://mjolnir.cs.ox.ac.uk/web/preface/index.php) as a backend.

# Basic usage

To use PMRSAbs, you just call it with your grammar file as argument:
    $ ./pmrsabs input.pmrs
    Successfull

PMRSAbs supports different modes:
* An evaluation mode, that stepwise reduces a given HORS (including determinization).
* A model checking mode for nondeterministic HORS and ATT
* A model checking mode for PMRS, HORS, and ATT

# Requirements

PMRSAbs needs several requirements to be built:
* Haskell platform
* An extension of data-multimap package (http://hub.darcs.net/arj/multimap)
* An extended version of Preface (not yet available)
* The Mono framework (needed for Preface)