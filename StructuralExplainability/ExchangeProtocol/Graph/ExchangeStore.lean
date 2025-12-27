import StructuralExplainability.ExchangeProtocol.Core.Record.Exchange.ExchangeRecord

namespace StructuralExplainability.ExchangeProtocol.Graph

structure ExchangeStore (Time : Type) where
  exchanges :
    List (StructuralExplainability.ExchangeProtocol.Core.Record.Exchange.ExchangeRecord Time)
  deriving Repr

/-- Convenience: the ID of an exchange record is its envelope.verifiableId. -/
def ExchangeStore.exchangeId {Time : Type}
  (e : StructuralExplainability.ExchangeProtocol.Core.Record.Exchange.ExchangeRecord Time) :
  StructuralExplainability.ExchangeProtocol.Core.Base.ExchangeId :=
  e.envelope.verifiableId

/-- Find an exchange by id (first match). -/
def ExchangeStore.findExchange? {Time : Type}
  (g : ExchangeStore Time)
  (id : StructuralExplainability.ExchangeProtocol.Core.Base.ExchangeId) :
  Option (StructuralExplainability.ExchangeProtocol.Core.Record.Exchange.ExchangeRecord Time) :=
  g.exchanges.find? (fun e => ExchangeStore.exchangeId e == id)

end StructuralExplainability.ExchangeProtocol.Graph
