import StructuralExplainability.ExchangeProtocol.Core.Base.Ids
import StructuralExplainability.ExchangeProtocol.Graph.TypedGraph

namespace StructuralExplainability.ExchangeProtocol.Graph

/-!
Exchange graph specialization.
-/

abbrev ExchangeId :=
  StructuralExplainability.ExchangeProtocol.Core.Base.ExchangeId

/-- The edge labels we care about for EP proofs. Extend as needed. -/
inductive ExchangeEdgeLabel where
  | dependsOn
  | derivedFrom
  | revises
  deriving Repr, BEq, DecidableEq

/-- An exchange graph is just a typed graph over ExchangeId. -/
abbrev ExchangeGraph :=
  TypedGraph ExchangeId ExchangeEdgeLabel

/-- Convenience predicate. -/
def HasDependency (g : ExchangeGraph) (upstream downstream : ExchangeId) : Prop :=
  TypedGraph.HasEdge g upstream downstream ExchangeEdgeLabel.dependsOn

/-
Reachability (downstream closure) for dependency edges only.
-/
inductive DependsPath (g : ExchangeGraph) : ExchangeId -> ExchangeId -> Prop where
  | step :
      ∀ a b,
        HasDependency g a b ->
        DependsPath g a b
  | trans :
      ∀ a b c,
        DependsPath g a b ->
        DependsPath g b c ->
        DependsPath g a c

/-- Acyclicity is a property, not assumed. -/
def Acyclic (g : ExchangeGraph) : Prop :=
  ∀ x, ¬ DependsPath g x x

end StructuralExplainability.ExchangeProtocol.Graph
