namespace StructuralExplainability.ExchangeProtocol.Core.Base

/-!
REQ:
  Shared primitive aliases used across Core modules.

OBS:
  Imports must appear before this comment (Lean requirement).
  Keep this file stable and semantics-free.
-/

abbrev Uri := String
abbrev DateTime := String
abbrev Sha256 := String

end StructuralExplainability.ExchangeProtocol.Core.Base
