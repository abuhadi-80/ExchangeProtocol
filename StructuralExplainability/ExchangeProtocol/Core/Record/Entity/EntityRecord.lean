import StructuralExplainability.ExchangeProtocol.Core.Base.Ids
import StructuralExplainability.ExchangeProtocol.Core.Model.Retention
import StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope
import StructuralExplainability.ExchangeProtocol.Core.Record.Shared.EntityRef

namespace StructuralExplainability.ExchangeProtocol.Core.Record.Entity

/-!
REQ:
  Schema mirror for: schemas/core/cep.entity.schema.json

OBS:
  This module defines the entity record (envelope + payload + optional retention).
-/

structure EntityPayload where
  entityId : StructuralExplainability.ExchangeProtocol.Core.Base.EntityId
  deriving Repr, BEq, DecidableEq

structure EntityRecord (TimePoint : Type) where
  envelope :
    StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope
  payload :
    EntityPayload
  retention :
    Option (StructuralExplainability.ExchangeProtocol.Core.Model.RetentionPolicy TimePoint) := none
  deriving Repr, BEq, DecidableEq

def EntityRecord.WellFormed {Time : Type} (x : EntityRecord Time) : Prop :=
  StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope.WellFormed
      x.envelope ∧
  x.envelope.recordKind =
    StructuralExplainability.ExchangeProtocol.Core.Shared.RecordKind.entity

end StructuralExplainability.ExchangeProtocol.Core.Record.Entity
