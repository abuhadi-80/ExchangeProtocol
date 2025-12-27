import StructuralExplainability.ExchangeProtocol.Core.Base.Ids

namespace StructuralExplainability.ExchangeProtocol.Core.Model

/-!
REQ:
  Retention policy primitives used by records that must model storage limits
  and deletion-eligibility in a structurally checkable way.

OBS:
  This module stays small and policy-agnostic: it provides only data shapes
  and structural predicates. Domain semantics live outside the core layer.

NOTE (Time dependency):
  Any record that includes `RetentionPolicy TimePoint` and derives `Repr/BEq/DecidableEq`
  will (correctly) require corresponding instances for `TimePoint`.
-/


/-- Structural basis under which retention is justified. -/
inductive RetentionBasis where
  | legalObligation
  | contractNecessity
  | consentBased
  | legitimateInterest
  | purposeActive
  deriving Repr, BEq, DecidableEq


/-- Optional time interval. Interpretation is external. -/
structure TimeInterval (TimePoint : Type) where
  start : TimePoint
  finish : TimePoint
  deriving Repr, BEq, DecidableEq


/-- Retention policy is a structural hook; it does not assert legality. -/
structure RetentionPolicy (TimePoint : Type) where
  basis : RetentionBasis
  period : Option (TimeInterval TimePoint) := none
  consentId :
    Option StructuralExplainability.ExchangeProtocol.Core.Base.ConsentId := none
  deriving Repr, BEq, DecidableEq


/--
Structural predicate indicating that retention has expired.

OBS:
  The meaning of "purpose fulfilled", "interest ended", or "contract ended"
  is supplied externally.

NOTE:
  `_now` is intentionally unused here; time comparison semantics are external.
-/
def RetentionExpired
  {TimePoint : Type}
  (policy : RetentionPolicy TimePoint)
  (_now : TimePoint)
  (consentWithdrawn :
    StructuralExplainability.ExchangeProtocol.Core.Base.ConsentId -> Prop)
  (purposeFulfilled : Prop := False)
  (interestEnded : Prop := False)
  (contractEnded : Prop := False)
  : Prop :=
  match policy.basis with
  | RetentionBasis.legalObligation =>
      False
  | RetentionBasis.contractNecessity =>
      contractEnded
  | RetentionBasis.consentBased =>
      match policy.consentId with
      | none => False
      | some c => consentWithdrawn c
  | RetentionBasis.legitimateInterest =>
      interestEnded
  | RetentionBasis.purposeActive =>
      purposeFulfilled


/--
If retention is consent-based and the anchored consent is withdrawn,
then retention is expired (structurally).
-/
theorem retention_expired_of_consent_withdrawn
  {TimePoint : Type}
  (policy : RetentionPolicy TimePoint)
  (now : TimePoint)
  (consentWithdrawn :
    StructuralExplainability.ExchangeProtocol.Core.Base.ConsentId -> Prop)
  (c : StructuralExplainability.ExchangeProtocol.Core.Base.ConsentId)
  (hbasis : policy.basis = RetentionBasis.consentBased)
  (hcid : policy.consentId = some c)
  (hwd : consentWithdrawn c)
  :
  RetentionExpired policy now consentWithdrawn := by
  unfold RetentionExpired
  simp [hbasis, hcid, hwd]

end StructuralExplainability.ExchangeProtocol.Core.Model
