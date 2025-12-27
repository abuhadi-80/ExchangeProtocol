namespace StructuralExplainability.ExchangeProtocol.Core.Base

/-!
REQ:
  Shared identifier aliases used across Core modules.

OBS:
  Imports must appear before this comment (Lean requirement).
  Keep this file stable and semantics-free.
-/

abbrev EntityId := String
abbrev RelationshipId := String
abbrev ExchangeId := String
abbrev ConsentId := String

end StructuralExplainability.ExchangeProtocol.Core.Base
