import StructuralExplainability.ExchangeProtocol.Core.Base.Primitives
import StructuralExplainability.ExchangeProtocol.Core.Base.Ids

namespace StructuralExplainability.ExchangeProtocol.Core.Model

/-!
REQ:
  Minimal context-tag data model.

WHY:
  Records may carry optional interpretive metadata without changing identity.

OBS:
  This file defines only the data shape; operations belong elsewhere.
-/

structure CTag where
  termUri : Option StructuralExplainability.ExchangeProtocol.Core.Base.Uri := none
  value : Option String := none
  deriving Repr, BEq, DecidableEq

end StructuralExplainability.ExchangeProtocol.Core.Model
