# Towards Computational UIP in Cubical Agda


This repository contains Agda Cubical code
for the proofs of preservation of square-filling properties:
homogeneous `SqFill` and heterogeneous `SqPFill`,
which are equivalent to UIP.
Currently, Pi, Sigma, Coproducts, and Path types are covered.

Here is a [clickable version](https://swampertx.github.io/hset-cubical/Everything.html) of the proofs.


## Usage

This code type checks in the [Cubical Agda without Glue](https://github.com/SwampertX/agda/tree/no-glue)
variant, which is in the process of merging into Agda.

If you are running it using `--cubical` instead of the `--cubical=no-glue`,
i.e. using mainline Agda,
just change all instances of `--cubical=no-glue` into `--cubical`.
In this case,
this code is checked with Agda 2.8.0 and Cubical Library 0.9.

If you want to try out the
[Cubical Agda without Glue](https://github.com/SwampertX/agda/tree/no-glue)
variant on this code,
you will have to manually change the `--cubical` flag in `Cubical.Foundations.Prelude`
to `--cubical=no-glue`.
