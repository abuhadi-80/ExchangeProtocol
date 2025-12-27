import StructuralExplainability.ExchangeProtocol.Core.Shared.RecordEnvelope

namespace StructuralExplainability.ExchangeProtocol.Core.Shared

def RecordEnvelope.ctagsOfType
  (env : RecordEnvelope)
  (typeUri : StructuralExplainability.ExchangeProtocol.Core.Base.Uri)
  : List StructuralExplainability.ExchangeProtocol.Core.Model.CTag :=
  match env.ctags with
  | none => []
  | some cts =>
      cts.filter (fun ct =>
        match ct.termUri with
        | none => false
        | some u => u == typeUri)

end StructuralExplainability.ExchangeProtocol.Core.Shared
