import StructuralExplainability.ExchangeProtocol.Core.Base.Primitives
import StructuralExplainability.ExchangeProtocol.Core.Model.CTag

namespace StructuralExplainability.ExchangeProtocol.Core.Shared

/-!
REQ:
  Shared record envelope used by all record kinds.

OBS:
  Keep shared types upstream and stable; do not grow this file with feature logic.
-/

-- Local aliases for Base primitives are stable and non-ambiguous
abbrev Date := String
abbrev VerifiableId := String

/-- recordKind enum from the schema. -/
inductive RecordKind where
  | entity
  | relationship
  | exchange
  | p3tag
  deriving Repr, BEq, DecidableEq

/-- status object from $defs.status. -/
structure RecordStatus where
  statusCode : String
  statusReason : Option String := none
  statusEffectiveDate : Date
  deriving Repr, BEq, DecidableEq

/-- timestamps object from $defs.timestamps. -/
structure RecordTimestamps where
  firstSeenAt : Option StructuralExplainability.ExchangeProtocol.Core.Base.DateTime := none
  lastUpdatedAt : StructuralExplainability.ExchangeProtocol.Core.Base.DateTime
  validFrom : StructuralExplainability.ExchangeProtocol.Core.Base.DateTime
  validTo : Option StructuralExplainability.ExchangeProtocol.Core.Base.DateTime := none
  deriving Repr, BEq, DecidableEq

/-- attestation object from $defs.attestation. -/
structure Attestation where
  attestationTimestamp : StructuralExplainability.ExchangeProtocol.Core.Base.DateTime
  attestorId : String
  verificationMethodUri :
      Option StructuralExplainability.ExchangeProtocol.Core.Base.Uri := none
  proofType : String
  proofPurpose : String
  proofValue : Option String := none
  sourceSystem : Option String := none
  sourceReference : Option String := none
  anchorUri : Option StructuralExplainability.ExchangeProtocol.Core.Base.Uri := none
  deriving Repr, BEq, DecidableEq

/-- Shared envelope for all records. -/
structure RecordEnvelope where
  recordKind : RecordKind
  recordSchemaUri : Option StructuralExplainability.ExchangeProtocol.Core.Base.Uri := none
  schemaVersion : String
  revisionNumber : Nat
  verifiableId : VerifiableId
  recordTypeUri : StructuralExplainability.ExchangeProtocol.Core.Base.Uri
  status : RecordStatus
  timestamps : RecordTimestamps
  attestations : List Attestation
  ctags : Option (List StructuralExplainability.ExchangeProtocol.Core.Model.CTag) := none
  deriving Repr, BEq, DecidableEq

/-- Structural constraints corresponding to key schema requirements. -/
def RecordEnvelope.WellFormed (env : RecordEnvelope) : Prop :=
  env.revisionNumber >= 1 ∧
  env.attestations ≠ []

/-- Minimal creation attestation (supports the global 1+ attestations invariant). -/
def Attestation.created
  (ts : StructuralExplainability.ExchangeProtocol.Core.Base.DateTime)
  : Attestation :=
  { attestationTimestamp := ts
    attestorId := "self"
    verificationMethodUri := none
    proofType := "created"
    proofPurpose := "creation"
    proofValue := none
    sourceSystem := none
    sourceReference := none
    anchorUri := none }

/--
Canonical constructor for a newly-created envelope.

OBS:
  revisionNumber is forced to be >= 1 (defaults to 1) via Nat.succ.
-/
def RecordEnvelope.mkCreated
  (recordKind : RecordKind)
  (schemaVersion : String)
  (verifiableId : VerifiableId)
  (recordTypeUri : StructuralExplainability.ExchangeProtocol.Core.Base.Uri)
  (status : RecordStatus)
  (timestamps : RecordTimestamps)
  (createdAt : StructuralExplainability.ExchangeProtocol.Core.Base.DateTime)
  (revisionNumber : Nat := 0)
  (recordSchemaUri : Option StructuralExplainability.ExchangeProtocol.Core.Base.Uri := none)
  (ctags : Option (List StructuralExplainability.ExchangeProtocol.Core.Model.CTag) := none)
  : RecordEnvelope :=
  { recordKind := recordKind
    recordSchemaUri := recordSchemaUri
    schemaVersion := schemaVersion
    revisionNumber := revisionNumber.succ
    verifiableId := verifiableId
    recordTypeUri := recordTypeUri
    status := status
    timestamps := timestamps
    attestations := [Attestation.created createdAt]
    ctags := ctags }

end StructuralExplainability.ExchangeProtocol.Core.Shared
