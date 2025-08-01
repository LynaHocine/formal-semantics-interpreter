# Formal Semantics OCaml Interpreter

This project contains an interpreter for a procedural language using **denotational semantics**, developed in OCaml.

It was submitted as part of the *Formal Semantics of Programming Languages* course (SS 2025).

## Files

- `assignment_b1.ml` — Interpreter implementing denotational semantics for expressions, commands, and procedures
- `optional_assignment_b1.ml` — Extended version implementing address-based memory model
- `Formal Semantics of Programming Languages_assignmentB1.pdf` — Assignment instructions and specification

## Features

- Expressions and commands using denotational semantics
- Procedures with input/output variables
- Optional memory-address-based variable handling
- Test program: Euclidean GCD + quotient accumulation

## How to Run

Open an OCaml terminal (`ocaml` or `utop`) and run:

```ocaml
#use "assignment_b1.ml";;

#use "optional_assignment_b1.ml";;
