import Std

namespace StructuralExplainability.ExchangeProtocol.Graph

/-
Std-only typed graph.
We represent a graph as:
- vertices : List V
- edges    : List (Edge V E)
No finiteness proofs needed; list form is concrete and easy to compute over.
-/

structure Edge (V : Type) (E : Type) where
  src   : V
  dst   : V
  label : E
  deriving Repr

/-- A concrete directed multigraph with edge labels. -/
structure TypedGraph (V : Type) (E : Type) where
  vertices : List V
  edges    : List (Edge V E)
  deriving Repr

/-- Membership predicate: an edge is in a graph. -/
def TypedGraph.HasEdge {V E : Type} (g : TypedGraph V E) (src dst : V) (lbl : E) : Prop :=
  Edge.mk src dst lbl ∈ g.edges

/-- Well-formedness: edges only mention declared vertices. -/
def TypedGraph.WellFormed {V E : Type} (g : TypedGraph V E) : Prop :=
  (∀ e ∈ g.edges, e.src ∈ g.vertices) ∧
  (∀ e ∈ g.edges, e.dst ∈ g.vertices)

end StructuralExplainability.ExchangeProtocol.Graph
