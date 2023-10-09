<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# A Formal Theory of Games of Incomplete Information Based on Belief Functions

**Update:** The ITP2023 formalization is available [on the ITP2023 branch](https://github.com/pPomCo/belgames/tree/ITP2023).

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/pPomCo/belgames/workflows/Docker%20CI/badge.svg?branch=main
[docker-action-link]: https://github.com/pPomCo/belgames/actions?query=workflow:"Docker%20CI"




We extend Bayesian games to the theory of belief functions. We
obtain a more expressive class of games we refer to as BelGames. It
makes it possible to better capture human behaviors with respect to
lack of information.
Next, we prove an extended version of the so-called
Howson--Rosenthal's theorem, showing that BelGames can be turned
into games of complete information, i.e., without any uncertainty.

## Meta

- Author(s):
  - Pierre Pomeret-Coquot (initial)
  - Erik Martin-Dorel (initial)
  - Hélène Fargier (initial)
- License: [MIT](LICENSE)
- Compatible Coq versions: 8.14 or later (use releases for other Coq versions)
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.13.0 or later (`algebra` suffices)
- Coq namespace: `BelGames`
- Related publication(s):
  - [Bel-Games: A Formal Theory of Games of Incomplete Information Based on Belief Functions in the Coq Proof Assistant (2022)](https://ut3-toulouseinp.hal.science/hal-03782650) 

## Building and installation instructions

The easiest way to install the latest released version of A Formal Theory of Games of Incomplete Information Based on Belief Functions
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-belgames
```

To instead build and install manually, do:

``` shell
git clone https://github.com/pPomCo/belgames.git
cd belgames
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



