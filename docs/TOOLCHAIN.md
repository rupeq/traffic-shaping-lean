# Reproducible Lean environment

The project uses Lean `leanprover/lean4:v4.33.1` and mathlib release `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474`. `formal/lean-toolchain` and `formal/lake-manifest.json` pin the toolchain and dependency revisions.

With the official Lean version manager installed:

```sh
cd formal
lake exe cache get
lake build
```

Installation instructions: <https://lean-lang.org/install/manual/>. The mathlib cache contains compiled dependencies; project proofs are checked by Lean when the project is built.

The initial local setup used the official Apple Silicon archive `lean-4.33.1-darwin_aarch64.tar.zst`, downloaded from the Lean release page. Its SHA-256 was verified against the GitHub release metadata:

```
88c45aad985b5d2a8d925fe10bd1296bd35f66f408480ab182d3facccd065a9d
```

Source: <https://github.com/leanprover/lean4/releases/tag/v4.33.1>.
