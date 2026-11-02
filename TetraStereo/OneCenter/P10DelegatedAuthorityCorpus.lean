import TetraStereo.OneCenter.P10NormativeAudit

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Frozen corpus for authorities delegated to by Blue Book P-10

P-10 is not a self-contained authority.  Its bibliography directs the reader to specialist
IUPAC/IUB or IUPAC/IUBMB recommendations.  This module records the exact nine publications behind
the eight non-Appendix dependency categories in `BlueBookP10Audit.ExternalAuthority`.

The source editions below are the official IUPAC Queen Mary web editions.  Several are compound
documents: normative text is split over HTML pages and chemical structures are separate image
resources.  Consequently, `bundleSha256` is not the digest of a landing page.  It is calculated by
sorting every downloaded artifact by its `./iupac.qmul.ac.uk/...` relative path, forming the same
`<artifact-sha256>  <relative-path>\n` records emitted by `sha256sum`, concatenating those records,
and taking SHA-256 once more.  `artifactCount`, `htmlCount`, and `imageCount` make omission of a
diagram detectable as well as a byte change.

These constants make the provenance claim precise and reproducible; Lean does not establish that
remote bytes have a particular digest.  Nor does source freezing constitute clause transcription.
The specialist clause audits therefore remain separate open obligations in the global manifest.
-/

namespace P10DelegatedAuthorityCorpus

/-- One specialist publication cited by P-10.  Carotenoid and retinoid nomenclature are separate
publications even though P-10 groups them under one subject dependency. -/
inductive Document where
  | steroid1989
  | carotenoid1974
  | retinoid1981
  | carbohydrate1996
  | aminoAcidPeptide1983
  | cyclitol1973
  | nucleicAcid1970
  | lipid1976
  | glycolipid1997
  deriving DecidableEq, Repr

namespace Document

def all : List Document :=
  [ .steroid1989
  , .carotenoid1974
  , .retinoid1981
  , .carbohydrate1996
  , .aminoAcidPeptide1983
  , .cyclitol1973
  , .nucleicAcid1970
  , .lipid1976
  , .glycolipid1997
  ]

@[simp] theorem mem_all (document : Document) : document ∈ all := by
  cases document <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 9 := by decide

/-- P-10 bibliography reference number in the 2013 Blue Book. -/
def blueBookReference : Document → Nat
  | .steroid1989 => 16
  | .carotenoid1974 => 40
  | .retinoid1981 => 49
  | .carbohydrate1996 => 27
  | .aminoAcidPeptide1983 => 18
  | .cyclitol1973 => 39
  | .nucleicAcid1970 => 47
  | .lipid1976 => 48
  | .glycolipid1997 => 50

def title : Document → String
  | .steroid1989 => "Nomenclature of Steroids (Recommendations 1989)"
  | .carotenoid1974 => "Nomenclature of Carotenoids (Rules Approved 1974)"
  | .retinoid1981 => "Nomenclature of Retinoids (Recommendations 1981)"
  | .carbohydrate1996 => "Nomenclature of Carbohydrates (Recommendations 1996)"
  | .aminoAcidPeptide1983 =>
      "Nomenclature and Symbolism for Amino Acids and Peptides (Recommendations 1983)"
  | .cyclitol1973 => "Nomenclature of Cyclitols (Recommendations 1973)"
  | .nucleicAcid1970 =>
      "Abbreviations and Symbols for Nucleic Acids, Polynucleotides and their Constituents " ++
        "(Recommendations 1970)"
  | .lipid1976 => "Nomenclature of Lipids (Recommendations 1976)"
  | .glycolipid1997 => "Nomenclature of Glycolipids (Recommendations 1997)"

/-- Canonical publication citation printed in the Blue Book bibliography. -/
def citation : Document → String
  | .steroid1989 => "Pure Appl. Chem. 61, 1783-1822 (1989)"
  | .carotenoid1974 => "Pure Appl. Chem. 41, 405-431 (1975)"
  | .retinoid1981 => "Pure Appl. Chem. 55, 721-726 (1983)"
  | .carbohydrate1996 => "Pure Appl. Chem. 68, 1919-2008 (1996)"
  | .aminoAcidPeptide1983 => "Pure Appl. Chem. 56, 595-624 (1984)"
  | .cyclitol1973 => "Pure Appl. Chem. 37, 283-297 (1974)"
  | .nucleicAcid1970 => "Pure Appl. Chem. 40, 277-290 (1974)"
  | .lipid1976 => "Eur. J. Biochem. 79, 11-21 (1977)"
  | .glycolipid1997 => "Pure Appl. Chem. 69, 2475-2487 (1997)"

/-- DOI of the cited publication when P-10 or the official web edition supplies one. -/
def doi? : Document → Option String
  | .steroid1989 => some "10.1351/pac198961101783"
  | .carotenoid1974 => some "10.1351/pac197541030405"
  | .retinoid1981 => some "10.1351/pac198355050721"
  | .carbohydrate1996 => some "10.1351/pac199668101919"
  | .aminoAcidPeptide1983 => some "10.1351/pac198456050595"
  | .cyclitol1973 => some "10.1351/pac197437010283"
  | .nucleicAcid1970 => some "10.1351/pac197440030277"
  | .lipid1976 => none
  | .glycolipid1997 => some "10.1351/pac199769122475"

def externalAuthority : Document → BlueBookP10Audit.ExternalAuthority
  | .steroid1989 => .steroidNomenclature
  | .carotenoid1974 | .retinoid1981 => .carotenoidAndRetinoidNomenclature
  | .carbohydrate1996 => .carbohydrateNomenclature
  | .aminoAcidPeptide1983 => .aminoAcidAndPeptideNomenclature
  | .cyclitol1973 => .cyclitolNomenclature
  | .nucleicAcid1970 => .nucleicAcidNomenclature
  | .lipid1976 => .lipidNomenclature
  | .glycolipid1997 => .glycolipidNomenclature

end Document

/-- How the official web edition was traversed to capture text and page-requisite diagrams. -/
inductive SnapshotTraversal where
  | recursiveNoParent
  | singlePageWithRequisites
  | singlePageWithRequisitesAndErrata
  deriving DecidableEq, Repr

structure Snapshot where
  rootUrl : String
  retrievalDate : String
  traversal : SnapshotTraversal
  artifactCount : Nat
  htmlCount : Nat
  imageCount : Nat
  bundleSha256 : String
  deriving DecidableEq, Repr

/-- Byte-level snapshot metadata.  The amino-acid bundle was refreshed on 2026-08-29 after
normalizing the official site's broken uppercase `AAADB.GIF` reference to the actually served
`AAadb.gif` resource; the other entries retain their 2026-08-11 captures. -/
def snapshot : Document → Snapshot
  | .steroid1989 =>
      { rootUrl := "https://iupac.qmul.ac.uk/steroid/"
        retrievalDate := "2026-08-11"
        traversal := .recursiveNoParent
        artifactCount := 100
        htmlCount := 23
        imageCount := 77
        bundleSha256 := "83cb309d8a3674ca7b6dfb90a0600a4a442aa17e3f3f2bcc898a705f06241210" }
  | .carotenoid1974 =>
      { rootUrl := "https://iupac.qmul.ac.uk/carot/"
        retrievalDate := "2026-08-11"
        traversal := .recursiveNoParent
        artifactCount := 52
        htmlCount := 4
        imageCount := 48
        bundleSha256 := "013686e2241d6a410e9ddd94796d395dd5ef3e2b5288db7f148d7be71390ed70" }
  | .retinoid1981 =>
      { rootUrl := "https://iupac.qmul.ac.uk/misc/ret.html"
        retrievalDate := "2026-08-11"
        traversal := .singlePageWithRequisitesAndErrata
        artifactCount := 17
        htmlCount := 2
        imageCount := 15
        bundleSha256 := "e7fdceac5572f5610d011019d44363b4c1f61a0cfd696ad4255ae0bd836d0f01" }
  | .carbohydrate1996 =>
      { rootUrl := "https://iupac.qmul.ac.uk/2carb/"
        retrievalDate := "2026-08-11"
        traversal := .recursiveNoParent
        artifactCount := 473
        htmlCount := 43
        imageCount := 430
        bundleSha256 := "f310af9535a0acf1f03997596188e9031ae2bda6a3366b51b535f387edc33413" }
  | .aminoAcidPeptide1983 =>
      { rootUrl := "https://iupac.qmul.ac.uk/AminoAcid/"
        retrievalDate := "record-54db71cc66a48d655191405c29c6a9ac"
        traversal := .recursiveNoParent
        artifactCount := 134
        htmlCount := 37
        imageCount := 97
        bundleSha256 := "f55486c6c8c24d545cde6387792b7ac77959476653ffd005f4d480572a8f808d" }
  | .cyclitol1973 =>
      { rootUrl := "https://iupac.qmul.ac.uk/cyclitol/"
        retrievalDate := "2026-08-11"
        traversal := .recursiveNoParent
        artifactCount := 51
        htmlCount := 4
        imageCount := 47
        bundleSha256 := "f4bcd60c0c370d90b7f907adccdc971df0ab26237e7bd77cd0d04597b2163927" }
  | .nucleicAcid1970 =>
      { rootUrl := "https://iupac.qmul.ac.uk/misc/naabb.html"
        retrievalDate := "2026-08-11"
        traversal := .singlePageWithRequisitesAndErrata
        artifactCount := 19
        htmlCount := 2
        imageCount := 17
        bundleSha256 := "bd3a192849390a891d4e9a67533205f02ae0fd473b730b2aa54dbbbf2cc7b508" }
  | .lipid1976 =>
      { rootUrl := "https://iupac.qmul.ac.uk/lipid/"
        retrievalDate := "2026-08-11"
        traversal := .recursiveNoParent
        artifactCount := 30
        htmlCount := 6
        imageCount := 24
        bundleSha256 := "9b223317b293897493272ef6b3b93695d15f2f6c856fb8472b1c4e286498ff68" }
  | .glycolipid1997 =>
      { rootUrl := "https://iupac.qmul.ac.uk/misc/glylp.html"
        retrievalDate := "2026-08-11"
        traversal := .singlePageWithRequisitesAndErrata
        artifactCount := 15
        htmlCount := 2
        imageCount := 13
        bundleSha256 := "a269ce3f407ae4226e3919b99a4f04c1f98069a180b952f89b998e8ff8bd2a58" }

/-- The Blue Book bibliography page that fixes references 16, 18, 27, 39, 40, and 47-50. -/
def blueBookReferenceMapUrl : String := "https://iupac.qmul.ac.uk/BlueBook/PDF/Refs.pdf"

def blueBookReferenceMapSha256 : String :=
  "4cf92eed547b0881a4b3fb17c58f0389bc3b5073d6f77bf614534e852a3a6727"

@[simp] theorem snapshot_artifact_partition (document : Document) :
    (snapshot document).htmlCount + (snapshot document).imageCount =
      (snapshot document).artifactCount := by
  cases document <;> decide

@[simp] theorem every_snapshot_nonempty (document : Document) :
    0 < (snapshot document).artifactCount := by
  cases document <;> decide

def documentsFor (authority : BlueBookP10Audit.ExternalAuthority) : List Document :=
  Document.all.filter fun document => document.externalAuthority = authority

/-- Every specialist dependency category has at least one exact publication.  Appendix 3 is
intentionally excluded: it is a Blue Book source already frozen by the global manifest. -/
theorem every_specialist_authority_has_document
    (authority : BlueBookP10Audit.ExternalAuthority)
    (notAppendix : authority ≠ .blueBookAppendix3) :
    ∃ document ∈ Document.all, document.externalAuthority = authority := by
  cases authority <;> simp_all [Document.all, Document.externalAuthority]

@[simp] theorem carotenoid_retinoid_authority_has_two_documents :
    documentsFor .carotenoidAndRetinoidNomenclature =
      [.carotenoid1974, .retinoid1981] := by
  decide

/-- A dependency is source-tracked either by the separately frozen Appendix 3 or by a specialist
publication in this corpus. -/
def SourceTracked (authority : BlueBookP10Audit.ExternalAuthority) : Prop :=
  authority = .blueBookAppendix3 ∨
    ∃ document ∈ Document.all, document.externalAuthority = authority

theorem every_external_authority_source_tracked
    (authority : BlueBookP10Audit.ExternalAuthority) : SourceTracked authority := by
  by_cases appendix : authority = .blueBookAppendix3
  · exact Or.inl appendix
  · exact Or.inr (every_specialist_authority_has_document authority appendix)

theorem every_recorded_p10_dependency_source_tracked
    (provision : BlueBookP10Audit.Provision)
    (authority : BlueBookP10Audit.ExternalAuthority)
    (_requires : BlueBookP10Audit.Requires provision authority) : SourceTracked authority :=
  every_external_authority_source_tracked authority

end P10DelegatedAuthorityCorpus

end TetraStereo.OneCenter
