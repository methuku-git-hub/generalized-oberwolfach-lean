module

public import Oberwolfach.MarkedVortexActiveRestrictedRimsColumnChanges
public import Oberwolfach.MarkedVortexParentRecordSmallerReferenceEvent
public import Oberwolfach.MarkedSpokeToleranceMonotone
public import Oberwolfach.RetainedMarkedSpokeGeometry

@[expose] public section
/-! The weighted smaller-reference parent event supplies the actual first-active
row, configuration and load fields for the same retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_active_transfer_from_smaller_parent
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (η B pstar:ℝ) (hζCfg:0<ζCfg) (hη:0<η) (hB:0≤B) (hpstar:0<pstar) (htstar:0<tstar):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀(G:SimpleGraph V) (Dnat mm:ℕ) (β ε:ℝ) (Q:Vortex U G Dnat β ε mm)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (L:ℕ) (s₀ p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
      (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
      (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
      (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
      (size a₀ b₀ e₀ f₀:ℕ)
      (hGood:MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d α ρ₀ sstar tstar kstar
        εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
        size a₀ b₀ e₀ f₀ G Dnat mm β ε Q π hπ L s₀ p k q s a j weightParent weight z)
      (τglobal:RawMarkedOutcome V U Γ Color) (Hglobal':Bool→V→U→Prop),
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let Z:=markedVortexNonDeeperHubType Q 0
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let ρ:=markedVortexActivePermutation Q π hπ 1
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g z.1
    let corrected:=rawMarkedRestrictPair f g τglobal
    let Hglobal:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let H':=fun b v u=>Hglobal' b (f v) (g u)
    let Dactive:=2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U Dnat
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let err:=τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*(4/ε)*ζWide;
    rawMarkedPairRims P ρ d corrected=rawMarkedPairRims P ρ d σ→
    ∀(FS:SimpleGraph (W⊕Z)),
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀u,(FS.degree (Sum.inr u):ℝ)≤ζ*Fintype.card W)→
    ∀(t βrec:ℝ),0<Fintype.card W→
    3*βrec≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*(2*ζCfg)→
    3*βrec≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*(2*ζCfg)→
    βrec≤t/4→tstar≤t→err≤η/8→ rowErr+ζRow≤tstar/16→
    (Fintype.card W:ℝ)/2≤Dactive→Dactive≤2*Fintype.card W→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) Dactive τ (successorWeightLower k₀ (α/4)) B (weight 1)→
    let fP:=markedVortexVertexEmbedding Q 0
    let gP:=markedVortexHubEmbedding Q 0
    let fA:=markedVortexNonDeeperVertexEmbedding Q 0
    let fnext:=markedVortexNextActiveInNonDeeper Q 0
    let gA:=markedVortexNonDeeperHubToParent Q 0
    let τP:=rawMarkedRestrictPair fP gP τglobal
    let HP:=fun b x u=>Hglobal' b (fP x) (gP u);
    MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d Finset.univ
      (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d 1 Finset.univ p k (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
      ((t/8)*Fintype.card W) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d (r+4) Dactive p k s₀ (weight 1) (η/4)
      (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) :=by
  obtain ⟨cap,hcap,htransfer⟩:=marked_vortex_initial_active_fields_restricted_rims_column_changes r (α/2) tstar kstar (2*ζCfg) η B pstar (by positivity) hη hB hpstar htstar
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ _ G Dnat mm β ε Q π hπ L s₀ p k q s a j weightParent weight z size a₀ b₀ e₀ f₀ hGood τglobal Hglobal' W Z f g ρ P σ corrected Hglobal H H' Dactive pstarLocal err hexact FS hS hFS t βrec hn hcycle hpath hβt htt herr hrowMargin hDlo hDhi hp hk hs hp1 hk1 hs1 hw fP gP fA fnext gA τP HP
  dsimp only [MarkedVortexParentRecordSmallerReferenceEvent] at hGood
  rcases hGood with ⟨hBal,hDeep,hActual,hAgree,hFull,hRow,hWide,hActive,hCommon,hConfig,hCut,hParent,hRecords⟩
  have hrow0:=hRow 0 (by omega)
  have hrow:=marked_rows_with_spokes_tolerance_mono P ρ d 1 Finset.univ p k (fun u=>q (g u)) (fun u=>s (g u)) a j
    ((rowErr+ζRow)*Fintype.card W) ((tstar/16)*Fintype.card W) σ H
    (mul_le_mul_of_nonneg_right hrowMargin (Nat.cast_nonneg _)) (by simpa only [Nat.zero_add] using hrow0)
  have hcfg:=hActive 0 (by omega)
  have hload:=hWide 0 (by omega)
  have htypes:∀v u,¬(Hglobal false v u∧Hglobal true v u):=by
    intro v u
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) a _ z.2 a j v u
  apply htransfer ζ hζ hζcap V U Γ Color G Dnat mm β ε Q π hπ d z.1 τglobal Hglobal Hglobal' htypes hexact FS hS hFS Dactive t τ (successorWeightLower k₀ (α/4)) err βrec p k s₀ (weight 1) q s a j hn hcycle hpath hβt htt herr hDlo hDhi hp hk hs hp1 hk1 hs1 hw hrow
  · simpa only [Nat.zero_add, show (2*ζCfg)/2=ζCfg by ring] using hcfg
  · simpa only [Nat.zero_add] using hload
end Oberwolfach
