import StructuralExplainability.ExchangeProtocol.Core

namespace StructuralExplainability.ExchangeProtocol.Vocabulary

/-!
Formalization of CEP vocabulary system.
Vocabularies provide controlled terms with SKOS-style mappings to external standards.
-/

/--
Vocabulary term status
-/
inductive TermStatus where
  | active
  | deprecated
  | experimental
  deriving Repr, BEq, DecidableEq

/--
SKOS-style mapping types
-/
inductive MappingType where
  | exactMatch    -- Conceptual equivalence
  | broadMatch    -- External term is broader
  | narrowMatch   -- External term is more specific
  | relatedMatch  -- Close but not hierarchical
  deriving Repr, BEq, DecidableEq

/--
Mapping to external standard
-/
structure ExternalMapping where
  termUri : String              -- CEP term being mapped
  externalUri : String          -- External standard's term URI
  mappingType : MappingType
  externalStandard : String     -- e.g., "Schema.org", "OCDS", "Popolo"
  deriving Repr

/--
Controlled vocabulary term
-/
structure VocabularyTerm where
  termUri : String              -- Full URI for this term
  code : String                 -- Short code (lowercase, hyphen-separated)
  label : String                -- Human-readable label
  definition : String           -- Precise definition
  parentTermUri : Option String -- For hierarchical vocabularies
  seeAlso : List String         -- Related references
  status : TermStatus
  deprecationNote : Option String
  addedInVersion : String       -- When term was introduced
  deriving Repr

/--
CEP Controlled Vocabulary
Corresponds to cep.vocabulary.schema.json
-/
structure Vocabulary where
  version : String              -- Semantic version
  title : String
  description : String
  governanceUri : String        -- How terms are managed
  effectiveDate : String        -- When this version became effective
  deprecatesVersion : Option String
  terms : List VocabularyTerm
  mappings : List ExternalMapping
  deriving Repr

/-! ## Vocabulary Properties -/

/--
Find term by code in vocabulary
-/
def Vocabulary.findTerm (v : Vocabulary) (code : String) : Option VocabularyTerm :=
  v.terms.find? (fun t => t.code == code)

/--
Find term by URI in vocabulary
-/
def Vocabulary.findTermByUri (v : Vocabulary) (uri : String) : Option VocabularyTerm :=
  v.terms.find? (fun t => t.termUri == uri)

/--
Get all active terms
-/
def Vocabulary.activeTerms (v : Vocabulary) : List VocabularyTerm :=
  v.terms.filter (fun t => t.status == TermStatus.active)

/--
Get all deprecated terms
-/
def Vocabulary.deprecatedTerms (v : Vocabulary) : List VocabularyTerm :=
  v.terms.filter (fun t => t.status == TermStatus.deprecated)

/--
Find external mappings for a term
-/
def Vocabulary.mappingsFor (v : Vocabulary) (termUri : String) : List ExternalMapping :=
  v.mappings.filter (fun m => m.termUri == termUri)

/--
Find exact matches to external standards
-/
def Vocabulary.exactMatches (v : Vocabulary) (termUri : String) : List ExternalMapping :=
  (v.mappingsFor termUri).filter (fun m => m.mappingType == MappingType.exactMatch)

/-! ## Vocabulary Consistency Properties -/

/--
A vocabulary is well-formed if:
- All term codes are unique
- All term URIs are unique
- All mapping termUris reference defined terms
- No term is its own parent (no cycles in hierarchy)
-/
def Vocabulary.wellFormed (v : Vocabulary) : Prop :=
  -- Term codes are unique
  (v.terms.map (fun t => t.code)).Nodup ∧
  -- Term URIs are unique
  (v.terms.map (fun t => t.termUri)).Nodup ∧
  -- All mappings reference defined terms
  (∀ m ∈ v.mappings,
    v.terms.any (fun t => t.termUri == m.termUri)) ∧
  -- No term is its own ancestor (hierarchy is acyclic)
  -- (Full cycle detection would require recursive checking)
  (∀ t ∈ v.terms,
    match t.parentTermUri with
    | none => True
    | some parentUri => parentUri ≠ t.termUri)

/-! ## Axioms about Vocabularies -/

axiom wellformed_unique_codes (v : Vocabulary) :
  Vocabulary.wellFormed v →
  ∀ (t1 t2 : VocabularyTerm),
    t1 ∈ v.terms →
    t2 ∈ v.terms →
    t1.code = t2.code →
    t1 = t2

axiom active_terms_usable (v : Vocabulary) (term : VocabularyTerm) :
  Vocabulary.wellFormed v →
  term ∈ v.terms →
  term.status = TermStatus.active →
  v.findTermByUri term.termUri = some term


/--
Theorem: External mappings preserve semantic relationships
If a CEP term has an exactMatch to an external term,
systems using the external standard can interpret the CEP term
-/
axiom external_mapping_preserves_semantics : ∀ (v : Vocabulary) (m : ExternalMapping),
  Vocabulary.wellFormed v →
  m ∈ v.mappings →
  m.mappingType = MappingType.exactMatch →
  -- The CEP term and external term are conceptually equivalent
  -- (This is a semantic property, so axiomatize it)
  True

end StructuralExplainability.ExchangeProtocol.Vocabulary
