# Coq-Cat
The repository contains formalizations of category theory. This is just for my personal studying.

## Setup
This version is known to compile with rocq-prover 9.0.0.

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create <opam-switch-name> 5.3.0
opam switch link <opam-switch-name> .
```
3. Add the Coq opam repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
```
4. Install the right version of the dependencies.
```
opam install rocq-prover.9.0.0
```

## How to Compile
You can compile this with the command below:
```
make -j
```

## Project Structure

This project is organized using Coq's logical path system, which is configured by the `Makefile` and the auto-generated `_CoqProject` file. The physical directories are mapped to logical Coq modules.

* **`Lib/`** (Mapped to `Category.Lib`) \
    This directory contains the core foundational library and utilities used throughout the project.

* **`Axioms/`** (Mapped to `Category.Axioms`) \
    This directory contains the axioms that underpin the formalization of category theory in this project.

* **`Algebra/`** (Mapped to `Category.Algebra`) \
    This directory contains algebraic structures and concepts that are relevant to category theory.

* **`Theory/`** (Mapped to `Category.Theory`) \
    This directory holds the formalization of category theory concepts.

* **`Instance/`** (Mapped to `Category.Instance`) \
    This directory holds the instances of `Category` typeclass.

* **`Construction/`** (Mapped to `Category.Construction`) \
    This directory contains various constructions in category theory. In other words, it includes ways to build new categories from existing ones.

* **`Facts/`** (Mapped to `Category.Facts`) \
    This directory contains various lemmas and definitions about categories and related structures, but is not part of the main theory development.

* **`imports/`** (Mapped to `Category`) \
    This directory serves as the main entry point for the project.

## Design Decisions
Some features and choices made in this library:
* **Typeclasses**: The library heavily relies on Coq's typeclass mechanism to define and manage categorical structures. This allows for more flexible and reusable code. When a type class instance would be too general, it is presented as a definition that can later be added to instance resolution with `Existing Instance`.
* **Type Universe**: All definitions are in `Type`, so that `Prop` is not used in the development. This increases the proof work necessary to establish certain properties, but it also allows for greater generality and applicability of the results.
* **Axioms**: Axioms are separated into their own directory (`Axioms/`) to clearly distinguish between foundational assumptions and derived results. Each axiom is presented as the form of typeclass, and this makes it easy to manage different sets of axioms for different contexts.