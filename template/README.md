# Template Tool

A Rust command-line tool for processing annotated Rocq templates to generate course assignments, solutions, and web materials.

## Overview

This tool processes Coq/Rocq template files with special annotations to generate different outputs for course management.

## Template syntax

Templates use special annotations in Rocq comments to control content generation. See the [test examples](./tests/examples) as well.

### Literate Documentation

- `(*| markdown content |*)` - Markdown blocks that get rendered to web documentation
- YAML frontmatter can be included in web-only blocks for page metadata

### Exercise/Solution Control

- `(* EXERCISE *)` ... `(* /EXERCISE *)` - Content shown only in student exercises
- `(* SOLUTION *)` ... `(* /SOLUTION *)` - Content shown only in instructor solutions
- `(* EXERCISE: Admitted. *)` - Single-line placeholder replaced with
  `Admitted.` in exercises, omitted in solutions; useful for text that needs to
  be commented out for the file to be a valid Rocq file.

### Web Generation Control

- `(* ONLY-WEB *)` ... `(* /ONLY-WEB *)` - Content included only when generating web materials
- `(* OMIT-WEB *)` ... `(* /OMIT-WEB *)` - Content excluded from web materials

### Example Template Structure

```coq
(* ONLY-WEB *)
(*| ---
category: lecture-note
tags: literate
order: 15
shortTitle: "Topic"
--- |*)
(* /ONLY-WEB *)

(*| # Title
This is markdown that appears in web documentation.
|*)

From sys_verif Require Import prelude.

(*| ## Exercise Section |*)

(* EXERCISE *)
Fail Definition broken_example := ...
(* /EXERCISE *)
(* SOLUTION *)
Definition working_example := ...
(* /SOLUTION *)

Lemma example_theorem : some_property.
Proof.
(* EXERCISE: Admitted. *)
  (* SOLUTION *)
  actual_proof_steps.
Qed.
```

This allows a single template file to generate:

- Student exercise files (with EXERCISE blocks, without SOLUTION blocks)
- Instructor solution files (with both EXERCISE and SOLUTION blocks)
- Web documentation (with literate markdown and metadata)

## Usage in Course

```bash
# Generate web materials
./etc/template literate -i src/sys_verif/notes/example.v -o web/example.md

# Create student assignments
./etc/template exercise src/sys_verif/assignments/hw1.v -o student-repo/hw1.v
```

## Commands

### `literate`

Convert literate Coq templates to markdown files for web publishing:

```bash
./etc/template literate -i input.v -o output.md --rocq-project _RocqProject
```

- Supports both exercise and solution modes (`--solution` flag)
- Uses Rocq/Coq project files for build configuration
- Includes SQLite caching for performance (`--no-cache` to disable)

### `repo`

Re-generate the student proofs repo:

```bash
./etc/template repo ../sys-verif-fa25-proofs
```
