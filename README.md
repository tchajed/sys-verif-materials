# Systems Verification materials

[![build](https://github.com/tchajed/sys-verif-materials/actions/workflows/build.yml/badge.svg)](https://github.com/tchajed/sys-verif-materials/actions/workflows/build.yml)

- `go/`: code to be verified
- `src/`: all Rocq proofs
  - `software_foundations/`: exercise files from Logical Foundations chapter of
    SF
  - `sys_verif/`: literate course notes and demos
  - `Goose/`: generated code from goose
- `template/`: tooling for compiling assignments, demos, and lecture notes
- `etc/` some scripts for managing this repo itself

The root directory has the Rocq setup (`Makefile`, `sys-verif.opam`,
`_RocqProject`) and VS Code setup (`.devcontainer`, `.vscode`).

## Updating things

```sh
./etc/template repo ../sys-verif-fa25-proofs
./etc/template web ../sys-verif-fa25
```

Update the Software Foundations exercises distributed in `src/software_foundations`:

```sh
./etc/update-lf.sh
```

## Including solutions

Assuming the private solutions repo is checked out adjacent to this repo:

```sh
ln -s $(realpath ../sys-verif-solutions/src/sys_verif/assignment_solns) src/sys_verif/
```

## Testing

```sh
make
```

```sh
cd template
cargo test
```

```sh
cd go
go test ./...
```

```sh
cd dafny
dafny verify *.dfy
dafny format --check *.dfy
```
