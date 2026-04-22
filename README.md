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
opam install coq-stdpp.1.12.0
opam install rocq-mathcomp-algebra.2.5.0
```

## How to Compile
You can compile this with the command below:
```
make -j
```
To clean the build files, use:
```
make clean
```

## Additional Notes
- The `Makefile` is configured to use `coq_makefile` to generate the necessary build files. If you want to customize the build process, you can modify the `Makefile` accordingly.
- The `theories/lib/sflib.v` file is a modified copy of the `src/sflib.v` file from the [sflib](https://github.com/snu-sf/sflib) repository. It is included here to avoid the notation conflict with the `mathcomp` library. If you want to use the latest version of `sflib`, you can replace this file with the one from the `sflib` repository, but be aware of potential conflicts.
- The `theories/core` directory contains the core definitions and lemmas of category theory, while the `theories/categories` directory contains specific categories and their properties. You can explore these directories to understand the structure of the formalization.