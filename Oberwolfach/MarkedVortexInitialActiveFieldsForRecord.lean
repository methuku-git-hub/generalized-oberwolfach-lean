module

public import Oberwolfach.MarkedVortexInitialActiveFieldsFromSelectedTests
public import Oberwolfach.MarkedVortexInitialRecordFieldsOfTransfers

@[expose] public section
/-! Align the transferred first-active fields with the initial record. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_initial_active_fields_for_record
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut:ℝ)    (hRaw:
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let ρ:=markedVortexActivePermutation Q π hpres 1
    let t:=s₀/((r+4:ℕ):ℝ)
    let Dactive:=2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D
    let fP:=markedVortexVertexEmbedding Q 0
    let gP:=markedVortexHubEmbedding Q 0
    let fA:=markedVortexNonDeeperVertexEmbedding Q 0
    let fnext:=markedVortexNextActiveInNonDeeper Q 0
    let gA:=markedVortexNonDeeperHubToParent Q 0
    let τP:=rawMarkedRestrictPair fP gP σglobal
    let HP:=fun b x u=>Hglobal b (fP x) (gP u);
    MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d Finset.univ
      (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d 1 Finset.univ p kval (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
      ((t/8)*Fintype.card W) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d (r+4) Dactive p kval s₀ (weight 1) (eta/4)
      (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u))):
    (let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:markedVortexNonDeeperHubType Q 0→markedVortexHubType Q 0:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres 0
      let ρ:=markedVortexActivePermutation Q π hpres (0+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (f x))) ρ d Finset.univ
        (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
        (fun b x u=>HP b (fA (f x)) (gA u))) ∧ (let Z:=markedVortexHubType Q 0
      let Zkeep:=markedVortexNonDeeperHubType Q 0
      let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:Zkeep→Z:=Subtype.val
      let ρ:=markedVortexActivePermutation Q π hpres (0+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
      MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d 1 Finset.univ p kval
        (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
        (((s₀/((r+4:ℕ):ℝ))/8)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (0+1)):Finset (markedVortexVertexType Q (0+1))))
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)) ∧
      MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d (r+4) ((2*(((Finset.univ\markedVortexInnerHubs Q (0+1)):Finset (markedVortexHubType Q (0+1))).card:ℝ)/initialIndexDensity U D)) p kval s₀ (weight (0+1)) (eta/4)
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))) :=by
  rcases hRaw with ⟨hconfig,hrow,hload⟩
  exact ⟨hconfig,hrow,hload⟩
end Oberwolfach
