/-
  RelParse — the relation-language CLI entry point for the `.ralg` interpreter.

  All of the tokenizer, parser, Boolean-matrix evaluator, and power-object operators live in the
  shared `rel.RelCore` module (which self-verifies its `#eval`/`example` demos at build time).
  This file is just the runnable `main` for the RELATION language (`obj`/`rel`/`let`/`print`,
  including `eps`/`Lambda`/`min`/`max`/`pow`).  The FOLD sub-language (`prog`/`run`, catamorphisms)
  has its own CLI in `rel.RelProg`; both import `rel.RelCore` and neither imports the other, so
  each can declare its own `_root_.main`.
-/
import rel.RelCore

/-- Entry point: read a `.ralg` path from the command line (default the division fixture),
    parse it, and run it.  Reads a REAL FILE via `IO.FS.readFile` — no compile-time IO.
    (`lean --run` / a compiled exe pass the argv tail as `args`.) -/
def main (args : List String) : IO Unit := do
  let path := args.getD 0 "rel/examples/division.ralg"
  let src ← IO.FS.readFile path
  Freyd.Alg.RAlg.runSource src
