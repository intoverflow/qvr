# qvr
Experiments in the quiver perspective

All code is written in [Lean](http://leanprover.github.io) version 3.


## What's going on here

A [category](https://ncatlab.org/nlab/show/category) is a data structure in modern math whose uses are many and varied. Categories can be used to model discrete structures (such as [partial orders](https://ncatlab.org/nlab/show/partial+order)), algebraic structures (such as [rings](https://ncatlab.org/nlab/show/ring)), logics (via [internal logics](https://ncatlab.org/nlab/show/internal+logic)), and other things. Categories are also used to "box up" entire theories, such as [the category of groups](https://ncatlab.org/nlab/show/Grp), [the category of topological spaces](https://ncatlab.org/nlab/show/Top), etc.

A [quiver](https://ncatlab.org/nlab/show/quiver) is a directed graph.

This project is a study in the use of these structures in modeling programming languages and related topics in computer science.


## Agenda

For our purposes, a programming language consists of (at a minimum) a *syntax* and a *semantics*. The syntax is assumed to be some kind of algebraic data, usually a term in a free algebra. The semantics is assumed to be a relation on the syntax.

To model a language, we take the syntax and semantics and bundle them up as a quiver: the vertices in the quiver are syntactically valid terms, and the arrows in the quiver represent the semantics.

The free category generated by this quiver models valid semantic traces in the language. From this quiver we may derive many things.

Functors from the free category into `PropCat` (the category of propositions) model runtime invariants. The [elements](https://ncatlab.org/nlab/show/category+of+elements) of such functors represent proofs that the invariants hold for a given syntactic term. For example, a *type theory* for a language consists of an algebra of such functors; the elements of the functors in such an algebra represent type judgments.

A compiler from language `L` to language `G` is a functor from the free category generated by `L` to the free category generated by `G`.

By the adjointness of the free category functor, a functor out of the free category is determined by its action on the arrows of the underlying quiver. This structure theorem makes these functors easy to define and work with.

In this project, we rigorize these ideas and explore their consequences.
