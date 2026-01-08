# Elementary Number Theory in Lean 4

Lean formalization of results from *Elementary Number Theory* (Gareth A. Jones and J. Mary Jones). The code targets Lean 4.26 and mathlib 4.26, and is organized by book chapters with theorem statements already encoded and proofs to be completed.

## Repo layout
- [ElementaryNumberTheory/ENT_all.lean](ElementaryNumberTheory/ENT_all.lean): AI-generated reference statements (Ch.1–11); **do not develop proofs here**.
- [ElementaryNumberTheory/Basic.lean](ElementaryNumberTheory/Basic.lean): scratch/demo file (currently a minimal placeholder).
- [ElementaryNumberTheory/Chapter1_Divisibility/en_chapter1.lean](ElementaryNumberTheory/Chapter1_Divisibility/en_chapter1.lean): formalization of Chapter 1 (statements and proofs **completed**).
- [ElementaryNumberTheory/Chapter1_Divisibility/EN_chapter1.md](ElementaryNumberTheory/Chapter1_Divisibility/EN_chapter1.md): natural-language statements and notes for Chapter 1.
- [ElementaryNumberTheory/Chapter2_Prime_Number/en_chapter2.lean](ElementaryNumberTheory/Chapter2_Prime_Number/en_chapter2.lean): formalization of Chapter 2 (statements complete, proofs **in progress**).
- [ElementaryNumberTheory/Chapter2_Prime_Number/EN_chapter2.md](ElementaryNumberTheory/Chapter2_Prime_Number/EN_chapter2.md): natural-language statements and notes for Chapter 2.

## Prerequisites
- Lean toolchain: 4.26.0 (pinned in [lean-toolchain](lean-toolchain)).
- Lake and mathlib (fetched automatically by Lake).
- VS Code with the Lean4 extension is recommended for interactive proof development.

## Setup
```powershell
# from the repo root
lake update          # fetch mathlib and dependencies
lake exe cache get   # optional: download prebuilt mathlib cache to speed up builds
lake build           # build the project
```

## Working on proofs
- Open the folder in VS Code, ensure the Lean4 language server starts, and work interactively.
- Replace `sorry` placeholders with proofs; search for remaining goals with `grep -n "sorry" ElementaryNumberTheory` or VS Code search.
- Keep imports minimal; most theorems already use `Mathlib` (and `Aesop`) in per-chapter files. Use [ElementaryNumberTheory/ENT_all.lean](ElementaryNumberTheory/ENT_all.lean) only as a reference for statements.
- Run `lake build` after edits to confirm everything compiles.

## Contribution guidelines
- Prefer concise lemma names mirroring the book numbering (e.g., `thm_1_1`, `cor_2_5`).
- Add brief comments only when the code is non-obvious; otherwise rely on descriptive names.
- Include small, focused commits with clear messages; push to `main` when checks pass.

## Next steps
- Chapter 1: done (see [ElementaryNumberTheory/Chapter1_Divisibility/en_chapter1.lean](ElementaryNumberTheory/Chapter1_Divisibility/en_chapter1.lean)).
- Chapter 2: continue filling proofs in [ElementaryNumberTheory/Chapter2_Prime_Number/en_chapter2.lean](ElementaryNumberTheory/Chapter2_Prime_Number/en_chapter2.lean).
- Later chapters: add per-chapter `.lean` following the pattern of Chapters 1–2; use ENT_all.lean only for a quick statement lookup.
