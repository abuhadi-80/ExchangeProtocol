import StructuralExplainability.ExchangeProtocol.Core.Base.Ids

namespace StructuralExplainability.ExchangeProtocol.Core.Model

/-!
REQ:
  Minimal consent model supporting withdrawal-based validity reasoning.

WHY:
  Consent is referenced by other records and graph rules.

OBS:
  Structural only; no policy, timing, or validation logic lives here.
-/

/-- Minimal consent lifecycle state. -/
inductive ConsentState where
  | Active
  | Withdrawn
  deriving Repr, BEq, DecidableEq

/-- Consent record (scaffold). -/
structure Consent where
  id : StructuralExplainability.ExchangeProtocol.Core.Base.ConsentId
  state : ConsentState
  deriving Repr, BEq, DecidableEq

end StructuralExplainability.ExchangeProtocol.Core.Model
