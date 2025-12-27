-- REQ.EXEC.MAIN:
--   Main entry point for this package.
--
-- WHY:
--   This executable exists solely to ensure that the full
--   formalization compiles end-to-end under CI and local builds.
--
-- OBS:
--   Imports MUST appear at the beginning of the file (Lean requirement).
--   No definitions, theorems, or logic belong here.
--   This file must remain trivial and stable.
--   Any failure here indicates a broken proof or import graph.

import StructuralExplainability

def main : IO Unit :=
  IO.println "Structural Explainability: package verified."
