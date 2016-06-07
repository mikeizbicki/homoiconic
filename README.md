            A spatial programming manifesto.
            --------------------------------

The bad news is that numerical programming in Haskell sucks.
The good news is that it doesn't have to.

Numerical programming in Haskell sucks.

Recent progress in numerical computing in Haskell has tried to make Haskell more like C.
But I want to make numerical computing in Haskell more like doing math with pencil and paper.

--------------------

Outline:

Section 1: The Method

    First, we define a type class hierarchy for topological spaces.

    Second, we reformalize the notion of a lawful type class in terms of topological spaces.

        * Eq for functions

    Third, we show how to automatically generate test cases for instances.

    Fourth, we define homomorphisms between type classes.

        * Topology's law is a homomorphism

    Fifth, we construct subcategories of Hask whose arrows are homomorphisms.

        * Linear algebra

        * Units?

        * Continuous functions

        * Differentiable functions/machine learning

Other:

    * Integration as folding

Section 2: The Examples:

    * Quotient types

    * Normal distributions and Gaussian processes.

    * MCMC monoid

    * Kalman filter vs. HMM?

    * Optimization methods?
