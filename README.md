<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Decision theoretic Coq project

**Update:** The ITP2023 formalization is available [on the ITP2023 branch](https://github.com/pPomCo/belgames/tree/ITP2023).

**Update:** The ITP2023 formalization is available [on the ITP2023 branch](https://github.com/pPomCo/belgames/tree/ITP2023).

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/pPomCo/belgames/workflows/Docker%20CI/badge.svg?branch=main
[docker-action-link]: https://github.com/pPomCo/belgames/actions?query=workflow:"Docker%20CI"


We formalize several results from uncertainty theories, decision theories and game theories.
The formalization offers some usable structures for set-functions (mass functions and capacities)

We also prove Howson and Rosenthal like transforms in a algebraic way and for generalized Bel-Games.
They cast games of incomplete information to games of complete information so they can be
studied with the classical game theoretic tools.


**Note 1:** *The ITP formalization has moved [on the ITP2023 branch](https://github.com/pPomCo/belgames/tree/ITP2023).*

**Note 2:** *This extended formalization match my PhD thesis which will be linked when published.*

## Meta

- Author(s):
  - Pierre Pomeret-Coquot (initial)
  - Erik Martin-Dorel (initial)
  - Hélène Fargier (initial)
- License: [MIT](LICENSE)
- Compatible Coq versions: 8.17 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 2.0 or later
- Coq namespace: `Decision`
- Related publication(s):
  - [Bel-Games: A Formal Theory of Games of Incomplete Information Based on Belief Functions in the Coq Proof Assistant (2022)](https://ut3-toulouseinp.hal.science/hal-03782650) 


To build and install manually, do:

``` shell
git clone https://github.com/pPomCo/belgames.git
cd belgames
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



