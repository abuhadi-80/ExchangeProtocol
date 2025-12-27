import StructuralExplainability.ExchangeProtocol.Graph.ExchangeStore

namespace StructuralExplainability.ExchangeProtocol.Graph.Dependency

open StructuralExplainability.ExchangeProtocol.Graph

def dependsOn {Time : Type}
  (g : ExchangeStore Time)
  (a b : StructuralExplainability.ExchangeProtocol.Core.Base.ExchangeId) : Prop :=
  ∃ e : StructuralExplainability.ExchangeProtocol.Core.Record.Exchange.ExchangeRecord Time,
    e ∈ g.exchanges ∧
    ExchangeStore.exchangeId e = a ∧
    match e.payload.dependsOnExchangeIds with
    | none => False
    | some deps => b ∈ deps

-- etc...

end StructuralExplainability.ExchangeProtocol.Graph.Dependency
