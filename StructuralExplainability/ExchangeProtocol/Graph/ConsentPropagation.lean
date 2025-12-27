import StructuralExplainability.ExchangeProtocol.Graph.ExchangeGraph
import StructuralExplainability.ExchangeProtocol.Core.Model.Consent

namespace StructuralExplainability.ExchangeProtocol.Graph

/-!
OBS:
  This file uses ExchangeId as the node identifier for all nodes in ExchangeGraph,
  including consent nodes. A future refinement may introduce Vertex := Sum ExchangeId ConsentId.
-/

abbrev Invalid :=
  ExchangeId -> Prop

abbrev ConsentStateOf :=
  ExchangeId -> StructuralExplainability.ExchangeProtocol.Core.Model.ConsentState

axiom invalid_of_direct_withdrawn_dependency
  (g : ExchangeGraph)
  (consentStateOf : ConsentStateOf)
  (Invalid : Invalid)
  :
  ∀ (e c : ExchangeId),
    HasDependency g e c ->
    consentStateOf c =
      StructuralExplainability.ExchangeProtocol.Core.Model.ConsentState.Withdrawn ->
    Invalid e

axiom invalid_propagates_upstream
  (g : ExchangeGraph)
  (Invalid : Invalid)
  :
  ∀ (x y : ExchangeId),
    HasDependency g x y ->
    Invalid y ->
    Invalid x

theorem invalid_of_withdrawn_dependency_closure
  (g : ExchangeGraph)
  (consentStateOf : ConsentStateOf)
  (Invalid : Invalid)
  :
  ∀ (e c : ExchangeId),
    DependsPath g e c ->
    consentStateOf c =
      StructuralExplainability.ExchangeProtocol.Core.Model.ConsentState.Withdrawn ->
    Invalid e := by
  intro e c hp hwithdrawn
  induction hp with
  | step a b hdep =>
      exact
        invalid_of_direct_withdrawn_dependency
          g consentStateOf Invalid a b hdep hwithdrawn
  | trans a b c hab hbc ih_ab ih_bc =>
      have hinv_b : Invalid b := ih_bc hwithdrawn
      have helper :
        ∀ (x y : ExchangeId), DependsPath g x y -> Invalid y -> Invalid x := by
          intro x y hxy hyinv
          induction hxy with
          | step u v huv =>
              exact invalid_propagates_upstream g Invalid u v huv hyinv
          | trans u v w huv hvw ih1 ih2 =>
              have inv_v : Invalid v := ih2 hyinv
              exact ih1 inv_v
      exact helper a b hab hinv_b

end StructuralExplainability.ExchangeProtocol.Graph
