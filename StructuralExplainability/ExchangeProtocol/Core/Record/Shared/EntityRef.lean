import StructuralExplainability.ExchangeProtocol.Core.Base.Primitives
import StructuralExplainability.ExchangeProtocol.Core.Base.Ids

namespace StructuralExplainability.ExchangeProtocol.Core.Record.Shared

/-!
REQ:
  Minimal entity reference used by record payloads.

WHY:
  Exchange, relationship, and other records reference entities
  without importing the full entity model.

OBS:
  Structural only; no validation or resolution logic lives here.
-/


/-- Lightweight reference to an entity. -/
structure EntityRef where
  entityId : StructuralExplainability.ExchangeProtocol.Core.Base.EntityId
  roleUri : Option StructuralExplainability.ExchangeProtocol.Core.Base.Uri := none
  accountIdentifier : Option String := none
  deriving Repr, BEq, DecidableEq

end StructuralExplainability.ExchangeProtocol.Core.Record.Shared
