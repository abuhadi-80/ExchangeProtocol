import StructuralExplainability.ExchangeProtocol.Core.Base.Ids
import StructuralExplainability.ExchangeProtocol.Core.Model.Retention
import StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope

namespace StructuralExplainability.ExchangeProtocol.Core.Record.Exchange

/-!
REQ:
  Schema mirror for: schemas/core/cep.exchange.schema.json

OBS:
  Structural only; no validation or resolution logic.
-/


abbrev Uri := StructuralExplainability.ExchangeProtocol.Core.Base.Uri
abbrev DateTime := StructuralExplainability.ExchangeProtocol.Core.Base.DateTime
abbrev Sha256 := StructuralExplainability.ExchangeProtocol.Core.Base.Sha256

abbrev RelationshipId := StructuralExplainability.ExchangeProtocol.Core.Base.RelationshipId
abbrev ExchangeId := StructuralExplainability.ExchangeProtocol.Core.Base.ExchangeId
abbrev ConsentId := StructuralExplainability.ExchangeProtocol.Core.Base.ConsentId


inductive ExchangeStatusCode where
  | PENDING
  | COMPLETED
  | REVERSED
  | CANCELED
  | DISPUTED
  deriving Repr, BEq, DecidableEq


structure ExchangeStatus where
  statusCode : ExchangeStatusCode
  statusEffectiveTimestamp : DateTime
  deriving Repr, BEq, DecidableEq


structure ExchangeValue where
  amount : Float
  currencyCode : Option String := none
  valueTypeUri : Option Uri := none
  inKindDescription : Option String := none
  deriving Repr, BEq


structure IntermediaryEntity where
  entityId : String
  roleUri : Option Uri := none
  deriving Repr, BEq, DecidableEq


structure ProvenanceChain where
  fundingChainTag : Option String := none
  ultimateSourceEntityId : Option String := none
  intermediaryEntities : Option (List IntermediaryEntity) := none
  parentExchangeId : Option String := none
  deriving Repr, BEq, DecidableEq


structure Categorization where
  cfdaNumber : Option String := none
  naicsCode : Option String := none
  gtasAccountCode : Option String := none
  localCategoryCode : Option String := none
  localCategoryLabel : Option String := none
  deriving Repr, BEq, DecidableEq


structure SourceReference where
  sourceSystemUri : Uri
  sourceRecordId : String
  sourceUrl : Option Uri := none
  deriving Repr, BEq, DecidableEq


structure ExchangePayload where
  relationshipId : RelationshipId
  exchangeTypeUri : Uri

  sourceEntity : String
  recipientEntity : String

  value : ExchangeValue
  occurredTimestamp : DateTime
  exchangeStatus : ExchangeStatus

  provenanceChain : Option ProvenanceChain := none
  categorization : Option Categorization := none
  sourceReferences : Option (List SourceReference) := none
  previousRecordHash : Option Sha256 := none

  dependsOnExchangeIds : Option (List ExchangeId) := none
  requiresConsentIds : Option (List ConsentId) := none
  deriving Repr, BEq


structure ExchangeRecord (Time : Type) where
  envelope : StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope
  payload : ExchangePayload
  retention :
    Option (StructuralExplainability.ExchangeProtocol.Core.Model.RetentionPolicy Time) := none
  deriving Repr, BEq


def ExchangeRecord.WellFormed {Time : Type} (x : ExchangeRecord Time) : Prop :=
  StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope.WellFormed x.envelope ∧
  x.envelope.recordKind =
    StructuralExplainability.ExchangeProtocol.Core.Shared.RecordKind.exchange

end StructuralExplainability.ExchangeProtocol.Core.Record.Exchange
