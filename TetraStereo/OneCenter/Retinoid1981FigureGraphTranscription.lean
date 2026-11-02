import TetraStereo.OneCenter.RetinoidStereochemistrySemantics
import TetraStereo.KernelOnly

set_option autoImplicit false
















namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace FigureGraphTranscription

structure FrozenImageData where
  artifact : SourceAudit.ImageArtifact
  relativePath : String
  sha256 : String
  width : Nat
  height : Nat
  deriving DecidableEq, Repr

def stereoparentSkeletonData : FrozenImageData :=
  { artifact := .stereoparentSkeleton
    relativePath := "miscgif/A2a.gif"
    sha256 := "58543774fc06a8b6b338a73f132535c8dd801b496be5cc18f6af4dfd087b7111"
    width := 205
    height := 97 }

/-- Exact per-GIF byte identities and source dimensions, in HTML occurrence order. -/
def frozenImageData : List FrozenImageData :=
  [ stereoparentSkeletonData
  , ⟨.glucuronideSubstituent, "miscgif/A2b.gif",
      "6cfdd7ae84348f6c8cac284dd28ad6e9abcd33e20dacadc609c6b5ad9673f03b", 170, 56⟩
  , ⟨.didehydroretinol, "miscgif/A43a.gif",
      "f6f0c638f616d9a8eb63254a72a301b54ca9da8aeea9dc0d1e8c5c0c1b0c2802", 232, 89⟩
  , ⟨.alphaVitaminA, "miscgif/A43b.gif",
      "62d70add0d9440b52f74b9211daf18f640ff24fc9062463f402849eaa721e114", 227, 89⟩
  , ⟨.epoxyDihydroretinol, "miscgif/A44a.gif",
      "4b279a2d7caa213fc438407084d2fbb1e80187c59d0bf02fdc7cdfd9c5f7ab6a", 227, 79⟩
  , ⟨.fluororetinoate, "miscgif/A44b.gif",
      "55d0acfcf6487c5815a398dc8b8ac61196164409b75cb78827a77d59e92884ec", 226, 79⟩
  , ⟨.secoRetinol, "miscgif/A45.gif",
      "27a1ae6fab00e6621455d4f34ec2a88f251681a15b8174e4d491a6083157a2f0", 281, 46⟩
  , ⟨.motretinideEtretinate, "miscgif/A46a.gif",
      "16c75932b462d83ca2008ac047f1822d2d30e1e66504a55178c49c404312f4aa", 261, 90⟩
  , ⟨.acetylDinorRetinoicAcid, "miscgif/A46b.gif",
      "588a00e36fbfe3bb342a13ef06db09c79f0c7267894ebd013b4e51ab88614bdf", 215, 102⟩
  , ⟨.anhydroVitaminA, "miscgif/A47a.gif",
      "8c25e2c1913758425bb25b9395c387fcb7deb3854c5bac730c0f465e9f0fcade", 199, 89⟩
  , ⟨.retroRetinylAcetate, "miscgif/A47b.gif",
      "0f97072447e94b431b88164251f634c032be06af40ea5f7bd2605c5e36bea699", 256, 88⟩
  , ⟨.hydroxyAcetoxyRetinol, "miscgif/A51.gif",
      "83f776bc2fb56ed6deeefa9ab9f622c85c51cb474ca507efda38278aca7a4796", 257, 81⟩
  , ⟨.cisRetinoidExamples, "miscgif/A52a.gif",
      "7963d85799d8caf7ffecc00e3d2e142304dd8d66bc4887ef67c5e05153c04cef", 182, 79⟩
  , ⟨.retroRetinalOxime, "miscgif/A52b.gif",
      "95bc9baa06a0abe357175d144f26047e682866760806df247aebf40cfba1818c", 234, 81⟩ ]

@[simp] theorem frozenImageData_count : frozenImageData.length = 14 := by decide

@[simp] theorem frozenImageArtifacts_exact :
    frozenImageData.map FrozenImageData.artifact =
      SourceAudit.ImageArtifact.chemicalFigures := by
  decide

theorem frozenImageArtifacts_nodup :
    (frozenImageData.map FrozenImageData.artifact).Nodup := by
  rw [frozenImageArtifacts_exact]
  decide

theorem frozenImagePaths_nodup :
    (frozenImageData.map FrozenImageData.relativePath).Nodup := by
  decide

inductive AtomElement where
  | carbon
  | nitrogen
  | oxygen
  | fluorine
  | genericSubstituent
  deriving DecidableEq, Repr

inductive BondOrder where
  | single
  | double
  deriving DecidableEq, Repr

structure AtomNode where
  locant : Nat
  element : AtomElement
  deriving DecidableEq, Repr

structure GraphBond where
  low : Nat
  high : Nat
  order : BondOrder
  deriving DecidableEq, Repr

namespace GraphBond

def edge (bond : GraphBond) : Nat × Nat :=
  (bond.low, bond.high)

end GraphBond

structure HeavyAtomGraph where
  nodes : List AtomNode
  bonds : List GraphBond
  deriving DecidableEq, Repr

namespace HeavyAtomGraph

def locants (graph : HeavyAtomGraph) : List Nat :=
  graph.nodes.map AtomNode.locant

def WellFormed (graph : HeavyAtomGraph) : Prop :=
  graph.locants.Nodup ∧
    graph.nodes.all (fun node => decide (0 < node.locant)) = true ∧
      (graph.bonds.map GraphBond.edge).Nodup ∧
        graph.bonds.all (fun bond =>
          decide (bond.low < bond.high) &&
            decide (bond.low ∈ graph.locants) &&
              decide (bond.high ∈ graph.locants)) = true

def wellFormed? (graph : HeavyAtomGraph) : Bool :=
  decide graph.locants.Nodup &&
    graph.nodes.all (fun node => decide (0 < node.locant)) &&
      decide (graph.bonds.map GraphBond.edge).Nodup &&
        graph.bonds.all (fun bond =>
          decide (bond.low < bond.high) &&
            decide (bond.low ∈ graph.locants) &&
              decide (bond.high ∈ graph.locants))

@[simp] theorem wellFormed?_eq_true_iff (graph : HeavyAtomGraph) :
    graph.wellFormed? = true ↔ graph.WellFormed := by
  simp [wellFormed?, WellFormed, and_assoc]

/-- A compact connectedness certificate specialized to source-numbered graphs: every atom after
locant 1 has an incident edge to a smaller locant.  Together with dense locants this gives a
construction path back to the root and catches isolated derivative atoms cheaply. -/
def everyNonrootLocantHasLowerNeighbor (graph : HeavyAtomGraph) : Bool :=
  graph.nodes.all fun node =>
    node.locant == 1 || graph.bonds.any fun bond =>
      bond.high == node.locant && decide (bond.low < node.locant)

end HeavyAtomGraph

private def carbon (locant : Nat) : AtomNode :=
  ⟨locant, .carbon⟩





def stereoparentSkeletonGraph : HeavyAtomGraph where
  nodes :=
    [ carbon 1, carbon 2, carbon 3, carbon 4, carbon 5
    , carbon 6, carbon 7, carbon 8, carbon 9, carbon 10
    , carbon 11, carbon 12, carbon 13, carbon 14, carbon 15
    , carbon 16, carbon 17, carbon 18, carbon 19, carbon 20 ]
  bonds :=
    [ ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 4, .single⟩, ⟨4, 5, .single⟩
    , ⟨5, 6, .double⟩, ⟨1, 6, .single⟩
    , ⟨6, 7, .single⟩, ⟨7, 8, .double⟩, ⟨8, 9, .single⟩, ⟨9, 10, .double⟩
    , ⟨10, 11, .single⟩, ⟨11, 12, .double⟩, ⟨12, 13, .single⟩
    , ⟨13, 14, .double⟩, ⟨14, 15, .single⟩
    , ⟨1, 16, .single⟩, ⟨1, 17, .single⟩, ⟨5, 18, .single⟩
    , ⟨9, 19, .single⟩, ⟨13, 20, .single⟩ ]

@[simp] theorem stereoparentSkeleton_locants_exact :
    stereoparentSkeletonGraph.nodes.map AtomNode.locant =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  rfl

@[simp] theorem stereoparentSkeleton_atom_count :
    stereoparentSkeletonGraph.nodes.length = 20 := by
  rfl

@[simp] theorem stereoparentSkeleton_bond_count :
    stereoparentSkeletonGraph.bonds.length = 20 := by
  rfl

@[simp] theorem stereoparentSkeleton_double_bond_count :
    (stereoparentSkeletonGraph.bonds.filter fun bond => bond.order == .double).length = 5 := by
  decide

theorem stereoparentSkeleton_wellFormed : stereoparentSkeletonGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

@[simp] theorem stereoparentSkeleton_lower_neighbor_chain :
    stereoparentSkeletonGraph.everyNonrootLocantHasLowerNeighbor = true := by
  decide

/-- A2a exactly as drawn: locant 15 is the printed terminal variable group `R`, while all other
numbered nodes and every bond retain the reusable skeleton's source numbering and connectivity. -/
def stereoparentFigureGraph : HeavyAtomGraph :=
  { nodes := stereoparentSkeletonGraph.nodes.map fun node =>
      if node.locant == 15 then { node with element := .genericSubstituent } else node
    bonds := stereoparentSkeletonGraph.bonds }

@[simp] theorem stereoparentFigureGraph_counts :
    stereoparentFigureGraph.nodes.length = 20 ∧
      stereoparentFigureGraph.bonds.length = 20 := by
  decide

@[simp] theorem stereoparentFigureGraph_numbering_and_connectivity_exact :
    stereoparentFigureGraph.nodes.map AtomNode.locant =
        stereoparentSkeletonGraph.nodes.map AtomNode.locant ∧
      stereoparentFigureGraph.bonds = stereoparentSkeletonGraph.bonds := by
  decide

@[simp] theorem stereoparentFigureGraph_locant15_is_generic :
    stereoparentFigureGraph.nodes.find? (fun node => node.locant == 15) =
      some ⟨15, .genericSubstituent⟩ := by
  decide

theorem stereoparentFigureGraph_wellFormed : stereoparentFigureGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

/-! ## Source-faithful derivative edit compiler -/

inductive GraphEdit where
  | addNode (node : AtomNode)
  | addBond (bond : GraphBond)
  | removeNode (atomId : Nat)
  | removeBond (low high : Nat)
  | setBondOrder (low high : Nat) (order : BondOrder)
  deriving DecidableEq, Repr

def applyEdit (graph : HeavyAtomGraph) : GraphEdit → HeavyAtomGraph
  | .addNode node => { graph with nodes := graph.nodes ++ [node] }
  | .addBond bond => { graph with bonds := graph.bonds ++ [bond] }
  | .removeNode atomId =>
      { nodes := graph.nodes.filter fun node => node.locant != atomId
        bonds := graph.bonds.filter fun bond => bond.low != atomId && bond.high != atomId }
  | .removeBond low high =>
      { graph with bonds := graph.bonds.filter fun bond =>
          !(decide (bond.low = low ∧ bond.high = high)) }
  | .setBondOrder low high order =>
      { graph with bonds := graph.bonds.map fun bond =>
          if bond.low = low ∧ bond.high = high then { bond with order := order } else bond }

def compileEdits (graph : HeavyAtomGraph) (edits : List GraphEdit) : HeavyAtomGraph :=
  edits.foldl applyEdit graph

private def oxygen (internalId : Nat) : AtomNode :=
  ⟨internalId, .oxygen⟩

/-- Retinol adds the terminal hydroxyl oxygen.  IDs above 20 are internal graph IDs for
un-numbered heteroatoms, not invented retinoid source locants. -/
def retinolGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [.addNode (oxygen 21), .addBond ⟨15, 21, .single⟩]

@[simp] theorem retinolGraph_counts :
    retinolGraph.nodes.length = 21 ∧ retinolGraph.bonds.length = 21 := by
  decide

def didehydroretinolGraph : HeavyAtomGraph :=
  compileEdits retinolGraph [.setBondOrder 3 4 .double]

def alphaVitaminAGraph : HeavyAtomGraph :=
  compileEdits retinolGraph
    [.setBondOrder 5 6 .single, .setBondOrder 4 5 .double]

def epoxyDihydroretinolGraph : HeavyAtomGraph :=
  compileEdits retinolGraph
    [ .setBondOrder 5 6 .single
    , .addNode (oxygen 22)
    , .addBond ⟨5, 22, .single⟩
    , .addBond ⟨6, 22, .single⟩ ]

def secoRetinolGraph : HeavyAtomGraph :=
  compileEdits retinolGraph
    [.removeBond 1 6, .setBondOrder 1 2 .double]

def doubleBondEdges (graph : HeavyAtomGraph) : List (Nat × Nat) :=
  (graph.bonds.filter fun bond => bond.order == .double).map GraphBond.edge

@[simp] theorem didehydroretinol_double_bonds_exact :
    doubleBondEdges didehydroretinolGraph =
      [(3, 4), (5, 6), (7, 8), (9, 10), (11, 12), (13, 14)] := by
  decide

@[simp] theorem alphaVitaminA_double_bonds_exact :
    doubleBondEdges alphaVitaminAGraph =
      [(4, 5), (7, 8), (9, 10), (11, 12), (13, 14)] := by
  decide

@[simp] theorem epoxyDihydroretinol_double_bonds_exact :
    doubleBondEdges epoxyDihydroretinolGraph =
      [(7, 8), (9, 10), (11, 12), (13, 14)] := by
  decide

@[simp] theorem secoRetinol_double_bonds_exact :
    doubleBondEdges secoRetinolGraph =
      [(1, 2), (5, 6), (7, 8), (9, 10), (11, 12), (13, 14)] := by
  decide

theorem first_derivative_graph_family_wellFormed :
    didehydroretinolGraph.WellFormed ∧
      alphaVitaminAGraph.WellFormed ∧
        epoxyDihydroretinolGraph.WellFormed ∧ secoRetinolGraph.WellFormed := by
  have didehydro : didehydroretinolGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have alpha : alphaVitaminAGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have epoxy : epoxyDihydroretinolGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have seco : secoRetinolGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  exact ⟨didehydro, alpha, epoxy, seco⟩

@[simp] theorem epoxyDihydroretinol_counts :
    epoxyDihydroretinolGraph.nodes.length = 22 ∧
      epoxyDihydroretinolGraph.bonds.length = 23 := by
  decide

@[simp] theorem secoRetinol_counts :
    secoRetinolGraph.nodes.length = 21 ∧ secoRetinolGraph.bonds.length = 20 := by
  decide

/-! ## Configuration-bearing figure family -/

private def fluorine (internalId : Nat) : AtomNode :=
  ⟨internalId, .fluorine⟩

/-- A44b: ethyl 12-fluororetinoate.  Internal nodes 21--24 are carbonyl oxygen, ester oxygen,
ethyl CH₂, and ethyl CH₃; node 25 is the printed fluorine at C-12. -/
def fluororetinoateGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (oxygen 21)
    , .addNode (oxygen 22)
    , .addNode (carbon 23)
    , .addNode (carbon 24)
    , .addNode (fluorine 25)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨15, 22, .single⟩
    , .addBond ⟨22, 23, .single⟩
    , .addBond ⟨23, 24, .single⟩
    , .addBond ⟨12, 25, .single⟩ ]

@[simp] theorem fluororetinoateGraph_counts :
    fluororetinoateGraph.nodes.length = 25 ∧
      fluororetinoateGraph.bonds.length = 25 := by
  decide

structure DoubleBondConfigurationClaim where
  low : Nat
  high : Nat
  parentGeometry : ParentGeometry
  ez : EZ
  deriving DecidableEq, Repr

namespace DoubleBondConfigurationClaim

def WellFormed (graph : HeavyAtomGraph) (claim : DoubleBondConfigurationClaim) : Prop :=
  (doubleBondEdges graph).contains (claim.low, claim.high) = true

end DoubleBondConfigurationClaim

def DoubleBondConfigurationClaimsWellFormed
    (graph : HeavyAtomGraph) (claims : List DoubleBondConfigurationClaim) : Prop :=
  claims.all (fun claim =>
    (doubleBondEdges graph).contains (claim.low, claim.high)) = true

/-- Ret-5.2's substitution example: parent-chain geometry remains trans at every bond, while
fluorine changes the CIP label at 11=12 from E to Z. -/
def fluororetinoateConfigurationClaims : List DoubleBondConfigurationClaim :=
  [ ⟨7, 8, .trans, .E⟩
  , ⟨9, 10, .trans, .E⟩
  , ⟨11, 12, .trans, .Z⟩
  , ⟨13, 14, .trans, .E⟩ ]

@[simp] theorem fluororetinoate_configuration_exact :
    fluororetinoateConfigurationClaims.map
      (fun claim => (claim.low, claim.high, claim.ez)) =
        [(7, 8, .E), (9, 10, .E), (11, 12, .Z), (13, 14, .E)] := by
  rfl

@[simp] theorem fluororetinoate_parent_geometry_unchanged :
    fluororetinoateConfigurationClaims.all
      (fun claim => claim.parentGeometry == .trans) = true := by
  decide

theorem fluororetinoate_configuration_wellFormed :
    DoubleBondConfigurationClaimsWellFormed
      fluororetinoateGraph fluororetinoateConfigurationClaims := by
  unfold DoubleBondConfigurationClaimsWellFormed
  decide

/-- A51, R=H: (3R)-3-hydroxyretinol. -/
def hydroxyRetinolGraph : HeavyAtomGraph :=
  compileEdits retinolGraph
    [.addNode (oxygen 22), .addBond ⟨3, 22, .single⟩]

/-- A51, R=COCH₃: (3R)-3-acetoxyretinol. -/
def acetoxyRetinolGraph : HeavyAtomGraph :=
  compileEdits hydroxyRetinolGraph
    [ .addNode (carbon 23)
    , .addNode (oxygen 24)
    , .addNode (carbon 25)
    , .addBond ⟨22, 23, .single⟩
    , .addBond ⟨23, 24, .double⟩
    , .addBond ⟨23, 25, .single⟩ ]

@[simp] theorem hydroxy_acetoxy_graph_atom_counts :
    hydroxyRetinolGraph.nodes.length = 22 ∧
      acetoxyRetinolGraph.nodes.length = 25 := by
  decide

structure CenterConfigurationClaim where
  atomId : Nat
  descriptor : RS
  deriving DecidableEq, Repr

namespace CenterConfigurationClaim

def WellFormed (graph : HeavyAtomGraph) (claim : CenterConfigurationClaim) : Prop :=
  graph.locants.contains claim.atomId = true

end CenterConfigurationClaim

def hydroxyAcetoxyCenterClaim : CenterConfigurationClaim :=
  ⟨3, .R⟩

@[simp] theorem hydroxyAcetoxyCenterClaim_exact :
    hydroxyAcetoxyCenterClaim.atomId = 3 ∧
      hydroxyAcetoxyCenterClaim.descriptor = .R := by
  decide

theorem hydroxy_acetoxy_center_claim_wellFormed :
    CenterConfigurationClaim.WellFormed hydroxyRetinolGraph hydroxyAcetoxyCenterClaim ∧
      CenterConfigurationClaim.WellFormed acetoxyRetinolGraph
        hydroxyAcetoxyCenterClaim := by
  unfold CenterConfigurationClaim.WellFormed
  decide

/-- A52a, R=CH₂OH: 13-cis-retinol. -/
def cisRetinolGraph : HeavyAtomGraph :=
  retinolGraph

/-- A52a, R=CO₂H: 13-cis-retinoic acid. -/
def cisRetinoicAcidGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .addNode (oxygen 21)
    , .addNode (oxygen 22)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨15, 22, .single⟩ ]

def cisRetinoidConfigurationClaims : List DoubleBondConfigurationClaim :=
  [ ⟨7, 8, .trans, .E⟩
  , ⟨9, 10, .trans, .E⟩
  , ⟨11, 12, .trans, .E⟩
  , ⟨13, 14, .cis, .Z⟩ ]

@[simp] theorem cisRetinoid_configuration_exact :
    cisRetinoidConfigurationClaims.map
      (fun claim => (claim.low, claim.high, claim.parentGeometry, claim.ez)) =
        [ (7, 8, .trans, .E)
        , (9, 10, .trans, .E)
        , (11, 12, .trans, .E)
        , (13, 14, .cis, .Z) ] := by
  rfl

theorem cisRetinoid_configuration_wellFormed :
    DoubleBondConfigurationClaimsWellFormed
        cisRetinolGraph cisRetinoidConfigurationClaims ∧
      DoubleBondConfigurationClaimsWellFormed
        cisRetinoicAcidGraph cisRetinoidConfigurationClaims := by
  unfold DoubleBondConfigurationClaimsWellFormed
  decide

theorem configured_figure_graph_family_wellFormed :
    fluororetinoateGraph.WellFormed ∧
      hydroxyRetinolGraph.WellFormed ∧
        acetoxyRetinolGraph.WellFormed ∧
          cisRetinolGraph.WellFormed ∧ cisRetinoicAcidGraph.WellFormed := by
  have fluoro : fluororetinoateGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have hydroxy : hydroxyRetinolGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have acetoxy : acetoxyRetinolGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have cisRetinol : cisRetinolGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have cisAcid : cisRetinoicAcidGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  exact ⟨fluoro, hydroxy, acetoxy, cisRetinol, cisAcid⟩

/-! ## Remaining heavy-atom figure family -/

private def nitrogen (internalId : Nat) : AtomNode :=
  ⟨internalId, .nitrogen⟩

private def genericSubstituent (internalId : Nat) : AtomNode :=
  ⟨internalId, .genericSubstituent⟩

/-- A2b: the printed β-D-glucopyranuronoyl substituent.  IDs 1--6 form the pyranose ring;
7--9 are its carboxylic acid, 10--12 the three free hydroxyl oxygens, and 13--16 the anomeric
O--CO--R linkage.  The generic continuation is retained rather than replaced by a fake atom. -/
def glucuronideSubstituentGraph : HeavyAtomGraph where
  nodes :=
    [ carbon 1, carbon 2, carbon 3, carbon 4, carbon 5, oxygen 6
    , carbon 7, oxygen 8, oxygen 9, oxygen 10, oxygen 11, oxygen 12
    , oxygen 13, carbon 14, oxygen 15, genericSubstituent 16 ]
  bonds :=
    [ ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 4, .single⟩
    , ⟨4, 5, .single⟩, ⟨5, 6, .single⟩, ⟨1, 6, .single⟩
    , ⟨5, 7, .single⟩, ⟨7, 8, .double⟩, ⟨7, 9, .single⟩
    , ⟨2, 10, .single⟩, ⟨3, 11, .single⟩, ⟨4, 12, .single⟩
    , ⟨1, 13, .single⟩, ⟨13, 14, .single⟩
    , ⟨14, 15, .double⟩, ⟨14, 16, .single⟩ ]

@[simp] theorem glucuronideSubstituentGraph_counts :
    glucuronideSubstituentGraph.nodes.length = 16 ∧
      glucuronideSubstituentGraph.bonds.length = 16 := by
  decide

/-- A46a: the shared graph behind motretinide (`R=NHC₂H₅`) and etretinate (`R=OC₂H₅`). -/
def motretinideEtretinateGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .removeNode 17
    , .setBondOrder 1 2 .double
    , .setBondOrder 3 4 .double
    , .addNode (oxygen 21)
    , .addNode (carbon 22)
    , .addNode (oxygen 23)
    , .addNode (genericSubstituent 24)
    , .addNode (carbon 25)
    , .addBond ⟨3, 21, .single⟩
    , .addBond ⟨21, 22, .single⟩
    , .addBond ⟨15, 23, .double⟩
    , .addBond ⟨15, 24, .single⟩
    , .addBond ⟨2, 25, .single⟩ ]

@[simp] theorem motretinideEtretinateGraph_counts :
    motretinideEtretinateGraph.nodes.length = 24 ∧
      motretinideEtretinateGraph.bonds.length = 24 := by
  decide

@[simp] theorem motretinideEtretinate_double_bonds_exact :
    doubleBondEdges motretinideEtretinateGraph =
      [ (1, 2), (3, 4), (5, 6), (7, 8), (9, 10)
      , (11, 12), (13, 14), (15, 23) ] := by
  decide

/-- A46b: 5-acetyl-4,18-dinor-retinoic acid.  Removing C-4 contracts the ring with the
source-implied 3--5 bond; removing C-18 deletes its incident methyl bond. -/
def acetylDinorRetinoicAcidGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .removeNode 4
    , .removeNode 18
    , .addBond ⟨3, 5, .single⟩
    , .addNode (oxygen 21)
    , .addNode (oxygen 22)
    , .addNode (carbon 23)
    , .addNode (oxygen 24)
    , .addNode (carbon 25)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨15, 22, .single⟩
    , .addBond ⟨5, 23, .single⟩
    , .addBond ⟨23, 24, .double⟩
    , .addBond ⟨23, 25, .single⟩ ]

@[simp] theorem acetylDinorRetinoicAcidGraph_counts :
    acetylDinorRetinoicAcidGraph.nodes.length = 23 ∧
      acetylDinorRetinoicAcidGraph.bonds.length = 23 := by
  decide

private def retroFourFourteenEdits : List GraphEdit :=
  [ .setBondOrder 5 6 .single
  , .setBondOrder 7 8 .single
  , .setBondOrder 9 10 .single
  , .setBondOrder 11 12 .single
  , .setBondOrder 13 14 .single
  , .setBondOrder 4 5 .double
  , .setBondOrder 6 7 .double
  , .setBondOrder 8 9 .double
  , .setBondOrder 10 11 .double
  , .setBondOrder 12 13 .double ]

/-- A47a: 4,5-didehydro-15,5-retro-deoxyretinol (anhydro vitamin A). -/
def anhydroVitaminAGraph : HeavyAtomGraph :=
  compileEdits stereoparentSkeletonGraph
    [ .setBondOrder 5 6 .single
    , .setBondOrder 7 8 .single
    , .setBondOrder 9 10 .single
    , .setBondOrder 11 12 .single
    , .setBondOrder 13 14 .single
    , .setBondOrder 4 5 .double
    , .setBondOrder 6 7 .double
    , .setBondOrder 8 9 .double
    , .setBondOrder 10 11 .double
    , .setBondOrder 12 13 .double
    , .setBondOrder 14 15 .double ]

@[simp] theorem anhydroVitaminA_double_bonds_exact :
    doubleBondEdges anhydroVitaminAGraph =
      [(4, 5), (6, 7), (8, 9), (10, 11), (12, 13), (14, 15)] := by
  decide

/-- A47b: 4,14-retro-retinyl acetate. -/
def retroRetinylAcetateGraph : HeavyAtomGraph :=
  compileEdits (compileEdits stereoparentSkeletonGraph retroFourFourteenEdits)
    [ .addNode (oxygen 21)
    , .addNode (carbon 22)
    , .addNode (oxygen 23)
    , .addNode (carbon 24)
    , .addBond ⟨15, 21, .single⟩
    , .addBond ⟨21, 22, .single⟩
    , .addBond ⟨22, 23, .double⟩
    , .addBond ⟨22, 24, .single⟩ ]

@[simp] theorem retroRetinylAcetate_double_bonds_exact :
    doubleBondEdges retroRetinylAcetateGraph =
      [(4, 5), (6, 7), (8, 9), (10, 11), (12, 13), (22, 23)] := by
  decide

/-- A52b: (6E,8E,10E,12E,15Z)-4,14-retro-retinal oxime. -/
def retroRetinalOximeGraph : HeavyAtomGraph :=
  compileEdits (compileEdits stereoparentSkeletonGraph retroFourFourteenEdits)
    [ .addNode (nitrogen 21)
    , .addNode (oxygen 22)
    , .addBond ⟨15, 21, .double⟩
    , .addBond ⟨21, 22, .single⟩ ]

@[simp] theorem retroRetinalOxime_double_bonds_exact :
    doubleBondEdges retroRetinalOximeGraph =
      [(4, 5), (6, 7), (8, 9), (10, 11), (12, 13), (15, 21)] := by
  decide

structure EZConfigurationClaim where
  low : Nat
  high : Nat
  ez : EZ
  deriving DecidableEq, Repr

def EZConfigurationClaimsWellFormed
    (graph : HeavyAtomGraph) (claims : List EZConfigurationClaim) : Prop :=
  claims.all (fun claim =>
    (doubleBondEdges graph).contains (claim.low, claim.high)) = true

def retroRetinalOximeConfigurationClaims : List EZConfigurationClaim :=
  [ ⟨6, 7, .E⟩, ⟨8, 9, .E⟩, ⟨10, 11, .E⟩, ⟨12, 13, .E⟩, ⟨15, 21, .Z⟩ ]

@[simp] theorem retroRetinalOxime_configuration_exact :
    retroRetinalOximeConfigurationClaims.map
      (fun claim => (claim.low, claim.high, claim.ez)) =
        [(6, 7, .E), (8, 9, .E), (10, 11, .E), (12, 13, .E), (15, 21, .Z)] := by
  rfl

theorem retroRetinalOxime_configuration_wellFormed :
    EZConfigurationClaimsWellFormed
      retroRetinalOximeGraph retroRetinalOximeConfigurationClaims := by
  unfold EZConfigurationClaimsWellFormed
  decide

theorem remaining_figure_graph_family_wellFormed :
    glucuronideSubstituentGraph.WellFormed ∧
      motretinideEtretinateGraph.WellFormed ∧
        acetylDinorRetinoicAcidGraph.WellFormed ∧
          anhydroVitaminAGraph.WellFormed ∧
            retroRetinylAcetateGraph.WellFormed ∧ retroRetinalOximeGraph.WellFormed := by
  have glucuronide : glucuronideSubstituentGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have motretinide : motretinideEtretinateGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have acetylDinor : acetylDinorRetinoicAcidGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have anhydro : anhydroVitaminAGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have retroAcetate : retroRetinylAcetateGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  have retroOxime : retroRetinalOximeGraph.WellFormed := by
    rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
    decide
  exact ⟨glucuronide, motretinide, acetylDinor, anhydro, retroAcetate, retroOxime⟩

/-! ## Proof-carrying artifact-to-graph catalog -/

inductive DenotationKind where
  | concreteMolecule
  | moleculeFamily
  deriving DecidableEq, Repr

/-- One source artifact and every distinct heavy-atom graph printed in that artifact.  A51 and
A52a each contain two structures; the other twelve chemical artifacts contain one. -/
structure FigureGraphFamilyEntry where
  artifact : SourceAudit.ImageArtifact
  /-- Constitutional graphs consumed by the authority-input compiler. -/
  graphs : List HeavyAtomGraph
  /-- Literal graphs rendered for source-figure comparison.  This differs from `graphs` only for
  A2a, whose printed terminal `R` is not one of the numbered 1--20 skeleton atoms. -/
  reviewGraphs : List HeavyAtomGraph
  denotationKind : DenotationKind
  deriving DecidableEq, Repr

namespace FigureGraphFamilyEntry

/-- Catalog admission requires an actual graph and structural validity for every family member. -/
def WellFormed (family : FigureGraphFamilyEntry) : Prop :=
  family.graphs ≠ [] ∧ family.graphs.Forall HeavyAtomGraph.WellFormed

end FigureGraphFamilyEntry

/-- Exact source-order catalog for the fourteen chemical GIFs.  This is the evidentiary source of
the live transcription frontier; adding an artifact name without its graph family is impossible. -/
def figureGraphFamilies : List FigureGraphFamilyEntry :=
  [ ⟨.stereoparentSkeleton, [stereoparentSkeletonGraph], [stereoparentFigureGraph], .moleculeFamily⟩
  , ⟨.glucuronideSubstituent, [glucuronideSubstituentGraph], [glucuronideSubstituentGraph], .moleculeFamily⟩
  , ⟨.didehydroretinol, [didehydroretinolGraph], [didehydroretinolGraph], .concreteMolecule⟩
  , ⟨.alphaVitaminA, [alphaVitaminAGraph], [alphaVitaminAGraph], .concreteMolecule⟩
  , ⟨.epoxyDihydroretinol, [epoxyDihydroretinolGraph], [epoxyDihydroretinolGraph], .concreteMolecule⟩
  , ⟨.fluororetinoate, [fluororetinoateGraph], [fluororetinoateGraph], .concreteMolecule⟩
  , ⟨.secoRetinol, [secoRetinolGraph], [secoRetinolGraph], .concreteMolecule⟩
  , ⟨.motretinideEtretinate, [motretinideEtretinateGraph], [motretinideEtretinateGraph], .moleculeFamily⟩
  , ⟨.acetylDinorRetinoicAcid, [acetylDinorRetinoicAcidGraph], [acetylDinorRetinoicAcidGraph], .concreteMolecule⟩
  , ⟨.anhydroVitaminA, [anhydroVitaminAGraph], [anhydroVitaminAGraph], .concreteMolecule⟩
  , ⟨.retroRetinylAcetate, [retroRetinylAcetateGraph], [retroRetinylAcetateGraph], .concreteMolecule⟩
  , ⟨.hydroxyAcetoxyRetinol, [hydroxyRetinolGraph, acetoxyRetinolGraph], [hydroxyRetinolGraph, acetoxyRetinolGraph], .moleculeFamily⟩
  , ⟨.cisRetinoidExamples, [cisRetinolGraph, cisRetinoicAcidGraph], [cisRetinolGraph, cisRetinoicAcidGraph], .moleculeFamily⟩
  , ⟨.retroRetinalOxime, [retroRetinalOximeGraph], [retroRetinalOximeGraph], .concreteMolecule⟩ ]

@[simp] theorem figureGraphFamilies_artifacts_exact :
    figureGraphFamilies.map FigureGraphFamilyEntry.artifact =
      SourceAudit.ImageArtifact.chemicalFigures := by
  decide

@[simp] theorem figureGraphFamilies_sizes_exact :
    figureGraphFamilies.map (fun family => family.graphs.length) =
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1] := by
  decide

@[simp] theorem figureGraphFamilies_denotationKinds_exact :
    figureGraphFamilies.map FigureGraphFamilyEntry.denotationKind =
      [ .moleculeFamily, .moleculeFamily, .concreteMolecule, .concreteMolecule
      , .concreteMolecule, .concreteMolecule, .concreteMolecule, .moleculeFamily
      , .concreteMolecule, .concreteMolecule, .concreteMolecule, .moleculeFamily
      , .moleculeFamily, .concreteMolecule ] := by
  decide

@[simp] theorem figureGraphFamily_count : figureGraphFamilies.length = 14 := by
  decide

@[simp] theorem transcribedGraph_count :
    (figureGraphFamilies.flatMap FigureGraphFamilyEntry.graphs).length = 16 := by
  decide

theorem figureGraphFamilies_all_wellFormed :
    figureGraphFamilies.Forall FigureGraphFamilyEntry.WellFormed := by
  rcases first_derivative_graph_family_wellFormed with
    ⟨didehydro, alpha, epoxy, seco⟩
  rcases configured_figure_graph_family_wellFormed with
    ⟨fluoro, hydroxy, acetoxy, cisRetinol, cisAcid⟩
  rcases remaining_figure_graph_family_wellFormed with
    ⟨glucuronide, motretinide, acetylDinor, anhydro, retroAcetate, retroOxime⟩
  simp [figureGraphFamilies, FigureGraphFamilyEntry.WellFormed,
    stereoparentSkeleton_wellFormed, glucuronide, didehydro, alpha, epoxy, fluoro, seco,
    motretinide, acetylDinor, anhydro, retroAcetate, hydroxy, acetoxy, cisRetinol, cisAcid,
    retroOxime]

@[simp] theorem reviewGraph_count :
    (figureGraphFamilies.flatMap FigureGraphFamilyEntry.reviewGraphs).length = 16 := by
  decide

theorem figureGraphFamilies_reviewGraphs_all_wellFormed :
    figureGraphFamilies.Forall fun family =>
      family.reviewGraphs ≠ [] ∧ family.reviewGraphs.Forall HeavyAtomGraph.WellFormed := by
  rcases first_derivative_graph_family_wellFormed with
    ⟨didehydro, alpha, epoxy, seco⟩
  rcases configured_figure_graph_family_wellFormed with
    ⟨fluoro, hydroxy, acetoxy, cisRetinol, cisAcid⟩
  rcases remaining_figure_graph_family_wellFormed with
    ⟨glucuronide, motretinide, acetylDinor, anhydro, retroAcetate, retroOxime⟩
  simp [figureGraphFamilies, stereoparentFigureGraph_wellFormed, glucuronide, didehydro,
    alpha, epoxy, fluoro, seco, motretinide, acetylDinor, anhydro, retroAcetate, hydroxy,
    acetoxy, cisRetinol, cisAcid, retroOxime]

/-- The initial family seed remains named separately from the live transcription frontier. -/
def seedTranscribedArtifacts : List SourceAudit.ImageArtifact :=
  [.stereoparentSkeleton]

/-- Exact historical frontier after the first four derivative edits. -/
def firstDerivativeTranscribedArtifacts : List SourceAudit.ImageArtifact :=
  [ .stereoparentSkeleton
  , .didehydroretinol
  , .alphaVitaminA
  , .epoxyDihydroretinol
  , .secoRetinol ]

/-- Exact historical frontier after adding the three configuration-bearing graph families. -/
def configuredTranscribedArtifacts : List SourceAudit.ImageArtifact :=
  [ .stereoparentSkeleton
  , .didehydroretinol
  , .alphaVitaminA
  , .epoxyDihydroretinol
  , .fluororetinoate
  , .secoRetinol
  , .hydroxyAcetoxyRetinol
  , .cisRetinoidExamples ]

/-- The live artifact frontier is derived from the concrete graph-family catalog. -/
def transcribedArtifacts : List SourceAudit.ImageArtifact :=
  figureGraphFamilies.map FigureGraphFamilyEntry.artifact

@[simp] theorem all_chemical_figure_heavy_atom_graphs_transcribed :
    transcribedArtifacts = SourceAudit.ImageArtifact.chemicalFigures := by
  exact figureGraphFamilies_artifacts_exact

@[simp] theorem transcribedArtifact_count : transcribedArtifacts.length = 14 := by
  decide

def pendingGraphTranscriptions : List SourceAudit.ImageArtifact :=
  SourceAudit.ImageArtifact.chemicalFigures.filter fun artifact =>
    !(decide (artifact ∈ transcribedArtifacts))

@[simp] theorem pendingGraphTranscription_count : pendingGraphTranscriptions.length = 0 := by
  decide

@[simp] theorem pendingGraphTranscriptions_empty : pendingGraphTranscriptions = [] := by
  decide

theorem graph_frontier_partition_exact :
    (transcribedArtifacts ++ pendingGraphTranscriptions).Perm
      SourceAudit.ImageArtifact.chemicalFigures := by
  decide

structure AutomatedInspection where
  reviewerIdentity : String
  reviewDate : String
  sourceBundleSha256 : String
  sourceBundleDigestMatched : Bool
  originalResolutionVisualReviewPerformed : Bool
  humanSignoffObtained : Bool
  heavyAtomGraphTranscriptionCount : Nat
  pendingGraphTranscriptionCount : Nat
  limitations : String
  deriving DecidableEq, Repr

def currentAutomatedInspection : AutomatedInspection where
  reviewerIdentity := "automated-record-383f307281f3e8334bf1a04ad8470f83"
  reviewDate := "record-5fef69c92fe2101683b1f8429852bf13"
  sourceBundleSha256 :=
    "e7fdceac5572f5610d011019d44363b4c1f61a0cfd696ad4255ae0bd836d0f01"
  sourceBundleDigestMatched := true
  originalResolutionVisualReviewPerformed := true
  humanSignoffObtained := false
  heavyAtomGraphTranscriptionCount := 14
  pendingGraphTranscriptionCount := 0
  limitations :=
    "automated-record-399405a4831d09a169d067374c196c2c" ++
    "record-075085c568ae8f4e424d0b0d4ba2c6ff" ++
    "record-f947c1de216b94054c0d605ddd95e509" ++
    "record-20ae15d6c1ebc56d90a74c65ec71348b"

@[simp] theorem current_automated_inspection_boundary_exact :
    currentAutomatedInspection.humanSignoffObtained = false ∧
      currentAutomatedInspection.heavyAtomGraphTranscriptionCount = 14 ∧
        currentAutomatedInspection.pendingGraphTranscriptionCount = 0 := by
  decide

end FigureGraphTranscription
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.frozenImageArtifacts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.stereoparentSkeleton_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.stereoparentSkeleton_lower_neighbor_chain
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.stereoparentFigureGraph_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.stereoparentFigureGraph_numbering_and_connectivity_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.stereoparentFigureGraph_locant15_is_generic
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.first_derivative_graph_family_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.configured_figure_graph_family_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.fluororetinoate_configuration_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.cisRetinoid_configuration_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.remaining_figure_graph_family_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.figureGraphFamilies_all_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.figureGraphFamilies_denotationKinds_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.figureGraphFamilies_reviewGraphs_all_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.retroRetinalOxime_configuration_wellFormed
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.graph_frontier_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureGraphTranscription.current_automated_inspection_boundary_exact
