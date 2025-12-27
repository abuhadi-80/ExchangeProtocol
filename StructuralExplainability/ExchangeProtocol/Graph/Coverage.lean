import StructuralExplainability.ExchangeProtocol.Graph.ExchangeGraph
import StructuralExplainability.ExchangeProtocol.Graph.TypedGraph

namespace StructuralExplainability.ExchangeProtocol.Graph

/-
Coverage lemmas for ExchangeGraph.

Goal: provide small, reusable facts that downstream theorems can rely on:
- if graph is WellFormed and an edge exists, endpoints are in vertices
- if DependsPath holds, endpoints are in vertices (under WellFormed)
-/

theorem edge_src_in_vertices
  (g : ExchangeGraph)
  (hWf : TypedGraph.WellFormed g)
  (e : Edge ExchangeId ExchangeEdgeLabel)
  (he : e ∈ g.edges)
  : e.src ∈ g.vertices := by
  exact hWf.left e he

theorem edge_dst_in_vertices
  (g : ExchangeGraph)
  (hWf : TypedGraph.WellFormed g)
  (e : Edge ExchangeId ExchangeEdgeLabel)
  (he : e ∈ g.edges)
  : e.dst ∈ g.vertices := by
  exact hWf.right e he

theorem dependency_endpoints_in_vertices
  (g : ExchangeGraph)
  (hWf : TypedGraph.WellFormed g)
  (a b : ExchangeId)
  (hDep : HasDependency g a b)
  : a ∈ g.vertices ∧ b ∈ g.vertices := by
  unfold HasDependency at hDep
  unfold TypedGraph.HasEdge at hDep
  have he : Edge.mk a b ExchangeEdgeLabel.dependsOn ∈ g.edges := hDep
  constructor
  · exact edge_src_in_vertices g hWf (Edge.mk a b ExchangeEdgeLabel.dependsOn) he
  · exact edge_dst_in_vertices g hWf (Edge.mk a b ExchangeEdgeLabel.dependsOn) he

theorem dependsPath_endpoints_in_vertices
  (g : ExchangeGraph)
  (hWf : TypedGraph.WellFormed g)
  (a b : ExchangeId)
  (hp : DependsPath g a b)
  : a ∈ g.vertices ∧ b ∈ g.vertices := by
  induction hp with
  | step a b hDep =>
      exact dependency_endpoints_in_vertices g hWf a b hDep
  | trans a b c hab hbc ih1 ih2 =>
      exact And.intro ih1.left ih2.right

end StructuralExplainability.ExchangeProtocol.Graph
