import TetraStereo.OneCenter.Basic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace TetraStereo.OneCenter















namespace BlueBookAppendix3Audit

inductive Alkaloid where
  | aconitane | ajmalan | akuammilan | alstophyllan | aporphine
  | aspidofractinine | aspidospermidine | atidane | atisine | berbaman | berbine
  | cephalotaxine | cevane | chelidonine | cinchonan | conanine | corynan | corynoxan
  | crinan | curan | daphnane | dendrobane | eburnamenine | emetan | ergoline
  | ergotaman | erythrinan | evonimine | evonine | formosanan | galanthamine
  | galanthan | hasubanan | hetisan | ibogamine | kopsan | lunarine | lycopodane
  | lycorenan | lythran | lythranidine | matridine | morphinan | nupharidine
  | ormosanine | oxayohimban18 | oxyacanthan | pancracine | rheadan | rodiasine
  | samandarine | sarpagan | senecionan | solanidane | sparteine | spirosolane
  | strychnidine | tazettine | tropane | tubocuraran | tubulosan | veratraman
  | vincaleukoblastine | vincane | vobasan | vobtusine | yohimban
  deriving DecidableEq, Repr

namespace Alkaloid

def all : List Alkaloid :=
  [ .aconitane, .ajmalan, .akuammilan, .alstophyllan, .aporphine
  , .aspidofractinine, .aspidospermidine, .atidane, .atisine, .berbaman, .berbine
  , .cephalotaxine, .cevane, .chelidonine, .cinchonan, .conanine, .corynan, .corynoxan
  , .crinan, .curan, .daphnane, .dendrobane, .eburnamenine, .emetan, .ergoline
  , .ergotaman, .erythrinan, .evonimine, .evonine, .formosanan, .galanthamine
  , .galanthan, .hasubanan, .hetisan, .ibogamine, .kopsan, .lunarine, .lycopodane
  , .lycorenan, .lythran, .lythranidine, .matridine, .morphinan, .nupharidine
  , .ormosanine, .oxayohimban18, .oxyacanthan, .pancracine, .rheadan, .rodiasine
  , .samandarine, .sarpagan, .senecionan, .solanidane, .sparteine, .spirosolane
  , .strychnidine, .tazettine, .tropane, .tubocuraran, .tubulosan, .veratraman
  , .vincaleukoblastine, .vincane, .vobasan, .vobtusine, .yohimban
  ]

@[simp] theorem mem_all (parent : Alkaloid) : parent ∈ all := by
  cases parent <;> simp [all]

theorem all_nodup : all.Nodup := by decide
@[simp] theorem all_length : all.length = 67 := by decide

def name : Alkaloid → String
  | .aconitane => "aconitane" | .ajmalan => "ajmalan" | .akuammilan => "akuammilan"
  | .alstophyllan => "alstophyllan" | .aporphine => "aporphine"
  | .aspidofractinine => "aspidofractinine" | .aspidospermidine => "aspidospermidine"
  | .atidane => "atidane" | .atisine => "atisine" | .berbaman => "berbaman"
  | .berbine => "berbine" | .cephalotaxine => "cephalotaxine" | .cevane => "cevane"
  | .chelidonine => "chelidonine" | .cinchonan => "cinchonan" | .conanine => "conanine"
  | .corynan => "corynan" | .corynoxan => "corynoxan" | .crinan => "crinan"
  | .curan => "curan" | .daphnane => "daphnane" | .dendrobane => "dendrobane"
  | .eburnamenine => "eburnamenine" | .emetan => "emetan" | .ergoline => "ergoline"
  | .ergotaman => "ergotaman" | .erythrinan => "erythrinan" | .evonimine => "evonimine"
  | .evonine => "evonine" | .formosanan => "formosanan" | .galanthamine => "galanthamine"
  | .galanthan => "galanthan" | .hasubanan => "hasubanan" | .hetisan => "hetisan"
  | .ibogamine => "ibogamine" | .kopsan => "kopsan" | .lunarine => "lunarine"
  | .lycopodane => "lycopodane" | .lycorenan => "lycorenan" | .lythran => "lythran"
  | .lythranidine => "lythranidine" | .matridine => "matridine" | .morphinan => "morphinan"
  | .nupharidine => "nupharidine" | .ormosanine => "ormosanine"
  | .oxayohimban18 => "18-oxayohimban" | .oxyacanthan => "oxyacanthan"
  | .pancracine => "pancracine" | .rheadan => "rheadan" | .rodiasine => "rodiasine"
  | .samandarine => "samandarine" | .sarpagan => "sarpagan" | .senecionan => "senecionan"
  | .solanidane => "solanidane" | .sparteine => "sparteine" | .spirosolane => "spirosolane"
  | .strychnidine => "strychnidine" | .tazettine => "tazettine" | .tropane => "tropane"
  | .tubocuraran => "tubocuraran" | .tubulosan => "tubulosan" | .veratraman => "veratraman"
  | .vincaleukoblastine => "vincaleukoblastine" | .vincane => "vincane"
  | .vobasan => "vobasan" | .vobtusine => "vobtusine" | .yohimban => "yohimban"

end Alkaloid

inductive Steroid where
  | androstane | bufanolide | campestane | cardanolide | cholane | cholestane
  | ergostane | estrane | furostan | gonane | gorgostane | poriferastane | pregnane
  | spirostan | stigmastane
  deriving DecidableEq, Repr

namespace Steroid

def all : List Steroid :=
  [ .androstane, .bufanolide, .campestane, .cardanolide, .cholane, .cholestane
  , .ergostane, .estrane, .furostan, .gonane, .gorgostane, .poriferastane, .pregnane
  , .spirostan, .stigmastane ]

@[simp] theorem mem_all (parent : Steroid) : parent ∈ all := by cases parent <;> simp [all]
theorem all_nodup : all.Nodup := by decide
@[simp] theorem all_length : all.length = 15 := by decide

def name : Steroid → String
  | .androstane => "androstane" | .bufanolide => "bufanolide"
  | .campestane => "campestane" | .cardanolide => "cardanolide"
  | .cholane => "cholane" | .cholestane => "cholestane" | .ergostane => "ergostane"
  | .estrane => "estrane" | .furostan => "furostan" | .gonane => "gonane"
  | .gorgostane => "gorgostane" | .poriferastane => "poriferastane"
  | .pregnane => "pregnane" | .spirostan => "spirostan" | .stigmastane => "stigmastane"

end Steroid

inductive Terpenoid where
  | abietane | ambrosane | aristolane | atisane | beyerane | bisabolane | bornane
  | cadinane | carane | caryophyllane | cedrane | dammarane | drimane | eremophilane
  | eudesmane | fenchane | gammacerane | germacrane | gibbane | grayanotoxane | guaiane
  | himachalane | hopane | humulane | kaurane | labdane | lanostane | lupane | pMenthane
  | oleanane | ophiobolane | picrasane | pimarane | pinane | podocarpane | protostane
  | retinal | rosane | taxane | thujane | trichothecane | ursane
  deriving DecidableEq, Repr

namespace Terpenoid

def all : List Terpenoid :=
  [ .abietane, .ambrosane, .aristolane, .atisane, .beyerane, .bisabolane, .bornane
  , .cadinane, .carane, .caryophyllane, .cedrane, .dammarane, .drimane, .eremophilane
  , .eudesmane, .fenchane, .gammacerane, .germacrane, .gibbane, .grayanotoxane, .guaiane
  , .himachalane, .hopane, .humulane, .kaurane, .labdane, .lanostane, .lupane, .pMenthane
  , .oleanane, .ophiobolane, .picrasane, .pimarane, .pinane, .podocarpane, .protostane
  , .retinal, .rosane, .taxane, .thujane, .trichothecane, .ursane ]

@[simp] theorem mem_all (parent : Terpenoid) : parent ∈ all := by cases parent <;> simp [all]
theorem all_nodup : all.Nodup := by decide
@[simp] theorem all_length : all.length = 42 := by decide

def name : Terpenoid → String
  | .abietane => "abietane" | .ambrosane => "ambrosane" | .aristolane => "aristolane"
  | .atisane => "atisane" | .beyerane => "beyerane" | .bisabolane => "bisabolane"
  | .bornane => "bornane" | .cadinane => "cadinane" | .carane => "carane"
  | .caryophyllane => "caryophyllane" | .cedrane => "cedrane" | .dammarane => "dammarane"
  | .drimane => "drimane" | .eremophilane => "eremophilane" | .eudesmane => "eudesmane"
  | .fenchane => "fenchane" | .gammacerane => "gammacerane" | .germacrane => "germacrane"
  | .gibbane => "gibbane" | .grayanotoxane => "grayanotoxane" | .guaiane => "guaiane"
  | .himachalane => "himachalane" | .hopane => "hopane" | .humulane => "humulane"
  | .kaurane => "kaurane" | .labdane => "labdane" | .lanostane => "lanostane"
  | .lupane => "lupane" | .pMenthane => "p-menthane" | .oleanane => "oleanane"
  | .ophiobolane => "ophiobolane" | .picrasane => "picrasane" | .pimarane => "pimarane"
  | .pinane => "pinane" | .podocarpane => "podocarpane" | .protostane => "protostane"
  | .retinal => "retinal" | .rosane => "rosane" | .taxane => "taxane"
  | .thujane => "thujane" | .trichothecane => "trichothecane" | .ursane => "ursane"

end Terpenoid

inductive Miscellaneous where
  | biline21H | cepham | corrin | flavan | isoflavan | lignane | neoflavan
  | neolignane33Prime | penam | porphyrin21H23H | prostane | thromboxane
  deriving DecidableEq, Repr

namespace Miscellaneous

def all : List Miscellaneous :=
  [ .biline21H, .cepham, .corrin, .flavan, .isoflavan, .lignane, .neoflavan
  , .neolignane33Prime, .penam, .porphyrin21H23H, .prostane, .thromboxane ]

@[simp] theorem mem_all (parent : Miscellaneous) : parent ∈ all := by
  cases parent <;> simp [all]
theorem all_nodup : all.Nodup := by decide
@[simp] theorem all_length : all.length = 12 := by decide

def name : Miscellaneous → String
  | .biline21H => "21H-biline" | .cepham => "cepham" | .corrin => "corrin"
  | .flavan => "flavan" | .isoflavan => "isoflavan" | .lignane => "lignane"
  | .neoflavan => "neoflavan" | .neolignane33Prime => "3,3'-neolignane"
  | .penam => "penam" | .porphyrin21H23H => "21H,23H-porphyrin"
  | .prostane => "prostane" | .thromboxane => "thromboxane"

end Miscellaneous

inductive CaroteneEndGroup where
  | beta | epsilon | gamma | phi | chi | kappa | psi
  deriving DecidableEq, Repr

namespace CaroteneEndGroup

def all : List CaroteneEndGroup := [.beta, .epsilon, .gamma, .phi, .chi, .kappa, .psi]

@[simp] theorem mem_all (group : CaroteneEndGroup) : group ∈ all := by
  cases group <;> simp [all]
theorem all_nodup : all.Nodup := by decide
@[simp] theorem all_length : all.length = 7 := by decide

def symbol : CaroteneEndGroup → String
  | .beta => "beta" | .epsilon => "epsilon" | .gamma => "gamma" | .phi => "phi"
  | .chi => "chi" | .kappa => "kappa" | .psi => "psi"

end CaroteneEndGroup

/-- All unordered pairs with repetition of the seven Appendix 3 carotene end groups. -/
inductive CaroteneParent where
  | betaBeta | betaEpsilon | betaGamma | betaPhi | betaChi | betaKappa | betaPsi
  | epsilonEpsilon | epsilonGamma | epsilonPhi | epsilonChi | epsilonKappa | epsilonPsi
  | gammaGamma | gammaPhi | gammaChi | gammaKappa | gammaPsi
  | phiPhi | phiChi | phiKappa | phiPsi
  | chiChi | chiKappa | chiPsi
  | kappaKappa | kappaPsi
  | psiPsi
  deriving DecidableEq, Repr

namespace CaroteneParent

def all : List CaroteneParent :=
  [ .betaBeta, .betaEpsilon, .betaGamma, .betaPhi, .betaChi, .betaKappa, .betaPsi
  , .epsilonEpsilon, .epsilonGamma, .epsilonPhi, .epsilonChi, .epsilonKappa, .epsilonPsi
  , .gammaGamma, .gammaPhi, .gammaChi, .gammaKappa, .gammaPsi
  , .phiPhi, .phiChi, .phiKappa, .phiPsi
  , .chiChi, .chiKappa, .chiPsi
  , .kappaKappa, .kappaPsi
  , .psiPsi
  ]

@[simp] theorem mem_all (parent : CaroteneParent) : parent ∈ all := by
  cases parent <;> simp [all]
theorem all_nodup : all.Nodup := by decide
@[simp] theorem all_length : all.length = 28 := by decide

def endGroups : CaroteneParent → CaroteneEndGroup × CaroteneEndGroup
  | .betaBeta => (.beta, .beta) | .betaEpsilon => (.beta, .epsilon)
  | .betaGamma => (.beta, .gamma) | .betaPhi => (.beta, .phi)
  | .betaChi => (.beta, .chi) | .betaKappa => (.beta, .kappa) | .betaPsi => (.beta, .psi)
  | .epsilonEpsilon => (.epsilon, .epsilon) | .epsilonGamma => (.epsilon, .gamma)
  | .epsilonPhi => (.epsilon, .phi) | .epsilonChi => (.epsilon, .chi)
  | .epsilonKappa => (.epsilon, .kappa) | .epsilonPsi => (.epsilon, .psi)
  | .gammaGamma => (.gamma, .gamma) | .gammaPhi => (.gamma, .phi)
  | .gammaChi => (.gamma, .chi) | .gammaKappa => (.gamma, .kappa)
  | .gammaPsi => (.gamma, .psi) | .phiPhi => (.phi, .phi) | .phiChi => (.phi, .chi)
  | .phiKappa => (.phi, .kappa) | .phiPsi => (.phi, .psi) | .chiChi => (.chi, .chi)
  | .chiKappa => (.chi, .kappa) | .chiPsi => (.chi, .psi)
  | .kappaKappa => (.kappa, .kappa) | .kappaPsi => (.kappa, .psi)
  | .psiPsi => (.psi, .psi)

theorem endGroups_injective : Function.Injective endGroups := by
  intro first second same
  cases first <;> cases second <;> simp_all [endGroups]

end CaroteneParent

inductive Stereoparent where
  | alkaloid (parent : Alkaloid)
  | steroid (parent : Steroid)
  | terpenoid (parent : Terpenoid)
  | carotene (parent : CaroteneParent)
  | miscellaneous (parent : Miscellaneous)
  deriving DecidableEq, Repr

namespace Stereoparent

def all : List Stereoparent :=
  Alkaloid.all.map .alkaloid ++ Steroid.all.map .steroid ++
    Terpenoid.all.map .terpenoid ++ CaroteneParent.all.map .carotene ++
    Miscellaneous.all.map .miscellaneous

@[simp] theorem mem_all (parent : Stereoparent) : parent ∈ all := by
  cases parent with
  | alkaloid parent => simp [all]
  | steroid parent => simp [all]
  | terpenoid parent => simp [all]
  | carotene parent => simp [all]
  | miscellaneous parent => simp [all]

theorem all_nodup : all.Nodup := by
  have alkaloids : (Alkaloid.all.map Stereoparent.alkaloid).Nodup :=
    Alkaloid.all_nodup.map (by intro left right equal; cases equal; rfl)
  have steroids : (Steroid.all.map Stereoparent.steroid).Nodup :=
    Steroid.all_nodup.map (by intro left right equal; cases equal; rfl)
  have terpenoids : (Terpenoid.all.map Stereoparent.terpenoid).Nodup :=
    Terpenoid.all_nodup.map (by intro left right equal; cases equal; rfl)
  have carotenes : (CaroteneParent.all.map Stereoparent.carotene).Nodup :=
    CaroteneParent.all_nodup.map (by intro left right equal; cases equal; rfl)
  have miscellaneous : (Miscellaneous.all.map Stereoparent.miscellaneous).Nodup :=
    Miscellaneous.all_nodup.map (by intro left right equal; cases equal; rfl)
  unfold all
  exact alkaloids.append
    (steroids.append
      (terpenoids.append
        (carotenes.append miscellaneous (by simp [List.disjoint_left]))
        (by simp [List.disjoint_left]))
      (by simp [List.disjoint_left]))
    (by simp [List.disjoint_left])

@[simp] theorem all_length : all.length = 164 := by
  simp [all]

def name : Stereoparent → String
  | .alkaloid parent => parent.name
  | .steroid parent => parent.name
  | .terpenoid parent => parent.name
  | .carotene parent =>
      let groups := parent.endGroups
      groups.1.symbol ++ "," ++ groups.2.symbol ++ "-carotene"
  | .miscellaneous parent => parent.name

end Stereoparent

inductive Provision where
  | stereoparentStructure (parent : Stereoparent)
  | caroteneEndGroupStructure (group : CaroteneEndGroup)
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  Stereoparent.all.map .stereoparentStructure ++
    CaroteneEndGroup.all.map .caroteneEndGroupStructure

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | stereoparentStructure parent => simp [all]
  | caroteneEndGroupStructure group => simp [all]

theorem all_nodup : all.Nodup := by
  have parents : (Stereoparent.all.map Provision.stereoparentStructure).Nodup :=
    Stereoparent.all_nodup.map (by intro left right equal; cases equal; rfl)
  have groups : (CaroteneEndGroup.all.map Provision.caroteneEndGroupStructure).Nodup :=
    CaroteneEndGroup.all_nodup.map (by intro left right equal; cases equal; rfl)
  unfold all
  exact parents.append groups (by simp [List.disjoint_left])

@[simp] theorem all_length : all.length = 171 := by
  simp [all]

def sourceKey : Provision → String
  | .stereoparentStructure parent => "Appendix 3/" ++ parent.name
  | .caroteneEndGroupStructure group => "Appendix 3/carotene-end-group/" ++ group.symbol

end Provision

inductive TranscriptionMaturity where
  | sourceOnly
  | molecularGraphTranscribed
  | configurationSemanticsReviewed
  deriving DecidableEq, Repr



def currentMaturity (_ : Provision) : TranscriptionMaturity := .sourceOnly

theorem no_appendix3_structure_yet_semantically_transcribed :
    ∀ provision, currentMaturity provision = .sourceOnly := by
  intro provision
  rfl



/-- Small manifest-facing constants keep checklist computation independent of the full dossier. -/
def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false

/-- Evidence from the separate source-fidelity pass over the exact reviewed Appendix-3 mirror.
All 29 rendered pages and all 171 enumerated entries were reviewed for captions, notes, naming
caveats, and the carotene composition rule. Molecular drawings remain deliberately outside this
prose/table claim and therefore keep the graph-transcription gate open. -/
structure SourceReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceArtifactSha256 : String
  reviewedRenderedPageNumbers : List Nat
  reviewedRenderedPages : Nat
  reviewedProvisions : List Provision
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceArtifactSha256Exact :
    sourceArtifactSha256 =
      "20c588c9d9bfd78f57d89bd7e0123bb1c9b0354191f80ace1f368e2b8290c962"
  reviewedRenderedPageNumbersExact :
    reviewedRenderedPageNumbers = (List.range 29).map (fun page => page + 1)
  reviewedRenderedPagesExact : reviewedRenderedPages = reviewedRenderedPageNumbers.length
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphTranscriptionsReviewedExact : figureGraphTranscriptionsReviewed = false

def currentSourceReview : SourceReviewEvidence where
  reviewerKind := "automated-record-ff5b7f6496e601ebe8a14c262136c4a1"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-144745a0d2aeca0cbda9daf8d109380f"
  sourceArtifactSha256 :=
    "20c588c9d9bfd78f57d89bd7e0123bb1c9b0354191f80ace1f368e2b8290c962"
  reviewedRenderedPageNumbers := (List.range 29).map (fun page => page + 1)
  reviewedRenderedPages := 29
  reviewedProvisions := Provision.all
  provisionEnumerationConfirmed := currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmed := currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := currentSourceReviewFigureGraphTranscriptionsReviewed
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  sourceArtifactSha256Exact := rfl
  reviewedRenderedPageNumbersExact := rfl
  reviewedRenderedPagesExact := by decide
  reviewedProvisionsExact := rfl
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphTranscriptionsReviewedExact := rfl

@[simp] theorem current_source_review_counts_and_gates_exact :
    currentSourceReview.reviewedRenderedPages = 29 ∧
      currentSourceReview.reviewedRenderedPageNumbers.length = 29 ∧
        currentSourceReview.reviewedProvisions.length = 171 ∧
          currentSourceReview.provisionEnumerationConfirmed = true ∧
            currentSourceReview.proseTableCoverageConfirmed = true ∧
              currentSourceReview.figureGraphTranscriptionsReviewed = false := by
  decide

end BlueBookAppendix3Audit

end TetraStereo.OneCenter
