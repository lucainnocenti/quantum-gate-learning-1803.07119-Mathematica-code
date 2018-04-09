# Content

Mathematica code used to reproduce the analytical results presented in "*Supervised learning of time-independent Hamiltonians for gate design*" ([arXiv:1803.07119](https://arxiv.org/abs/1803.07119)).
***This repo is still a work in progress***.

# Use
To use the packages and notebooks in here the [`QM`](https://github.com/lucainnocenti/QM) package is required.

## Packages
- [`QPauliAlgebra.m`](./QPauliAlgebra.m): Mathematica *package* defining the core functionality to handle symbolic pauli algebras. Here is where functions such as `QPauliExpr` are defined. The notebooks `QPauliAlgebraTests.nb` and `QPauliAlgebraExamples.nb` contain unit tests and usage examples for some of these functions, respectively.
- [`GateLearning.m`](./GateLearning.m): Mathematica package defining the functions to decompose matrices in the Pauli representation, extract generators as pauli expressions etc. It also contains functions to apply the three conditions shown in the paper.
The notebook `GateLearningTests.nb` contains some unit tests checking core functionalities of this package.

## Notebooks
- [`FredkinConditions.nb`](./FredkinConditions.nb): Contains the code used to obtain the analytical expressions for the Fredkin generator with only diagonal pairwise interactions.
- [`TestToffoliAndCCZ.nb`](./TestToffoliAndCCZ.nb): Contains some (failed) attempts at finding analytically generators for Toffoli and CCZ with only diagonal interactions.
Some of the code here may not be working properly now due to updates to the code in the supporting packages.
