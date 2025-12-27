import StructuralExplainability.ExchangeProtocol.Core.Base.Ids
import StructuralExplainability.ExchangeProtocol.Core.Model.Retention
import StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope
import StructuralExplainability.ExchangeProtocol.Core.Record.Shared.EntityRef

namespace StructuralExplainability.ExchangeProtocol.Core.Record.Relationship

structure RelationshipPayload where
  relationshipId : StructuralExplainability.ExchangeProtocol.Core.Base.RelationshipId

  subjectEntity : StructuralExplainability.ExchangeProtocol.Core.Record.Shared.EntityRef
  objectEntity  : StructuralExplainability.ExchangeProtocol.Core.Record.Shared.EntityRef

  relationshipTypeUri : StructuralExplainability.ExchangeProtocol.Core.Base.Uri
  sourceReferences : Option (List StructuralExplainability.ExchangeProtocol.Core.Base.Uri) := none

  deriving Repr, BEq, DecidableEq


structure RelationshipRecord (TimePoint : Type) where
  envelope :
    StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope
  payload :
    RelationshipPayload
  retention :
    Option (StructuralExplainability.ExchangeProtocol.Core.Model.RetentionPolicy TimePoint) := none
  deriving Repr, BEq, DecidableEq


def RelationshipRecord.WellFormed {TimePoint : Type} (x : RelationshipRecord TimePoint) : Prop :=
  StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope.WellFormed x.envelope ∧
  x.envelope.recordKind =
    StructuralExplainability.ExchangeProtocol.Core.Shared.RecordKind.relationship

end StructuralExplainability.ExchangeProtocol.Core.Record.Relationship
