module

public import Oberwolfach.MarkedVortexInitialRecordFields

@[expose] public section
/-! Assemble the actual initial record from the separately transferred
common, parent, active, potential, balance, cut and boundary fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_initial_record_fields_of_transfers
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut:ℝ)    (hCommon: (let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:markedVortexNonDeeperHubType Q 0→markedVortexHubType Q 0:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres 0
      let ρ:=markedVortexActivePermutation Q π hpres (0+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
MarkedCommonConfigurationsWithSpokes r (G.comap fP) ρP d βA (κ/4) σP HP) ∧ (let W:=markedVortexVertexType Q 0; let Z:=markedVortexHubType Q 0
      let f:=markedVortexVertexEmbedding Q 0; let g:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0; let σ:=rawMarkedRestrictPair f g σglobal
      let H:=fun b x u=>Hglobal b (f x) (g u);
      MarkedRowsWithSpokes (G.comap f) ρ d (r+12) Finset.univ p kval (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W)) ∧ (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let f:=markedVortexVertexEmbedding Q 0
      let g:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0
      let rho:=initialIndexDensity U D
      let c:ℝ:=(r+4:ℕ)
      let t:=s₀/c
      let pRef:=rho*c*t/2
      let kRef:=pRef/c
      let DRef:=2*(Fintype.card Z:ℝ)/rho
      let σ:=rawMarkedRestrictPair f g σglobal;
      MarkedReferenceStatistics (G.comap f) ρ d a j DRef (κ/4) κ (2*(α/16)) pRef kRef (c*t) t σ ∧
      MarkedReferenceCutFamilies (G.comap f) ρ d a j (2*(α/16)) pRef kRef t σ))
    (hDeep: (let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:markedVortexNonDeeperHubType Q 0→markedVortexHubType Q 0:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres 0
      let ρ:=markedVortexActivePermutation Q π hpres (0+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
MarkedLocalConfigurationsWithSpokes r (G.comap fP) ρP d Finset.univ
        (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) σP HP) ∧ (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let P:=G.comap (markedVortexVertexEmbedding Q 0)
      let ρ:=markedVortexPermutation Q π hpres 0
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal
      let H:=fun b x u=>Hglobal b
        (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q 0 u)
      let si:=fun u=>s (markedVortexHubEmbedding Q 0 u);
MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent 0) (thetaDeep/4) σ H))
    (hActive: (let fP:=markedVortexVertexEmbedding Q 0
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
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))))
    (hPotential: (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let P:=G.comap (markedVortexVertexEmbedding Q 0)
      let ρ:=markedVortexPermutation Q π hpres 0
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal
      let H:=fun b x u=>Hglobal b
        (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q 0 u)
      let si:=fun u=>s (markedVortexHubEmbedding Q 0 u);
(let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd (r+4) ρ (3*d)
          (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weightParent 0 X.1.val/(Dload*p^(r+4)*kval*s₀^(r+4));
        ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
          rawMarkedWheelMarginal P ρ d p kval qi si a j root≠0→
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1|≤κ/4)))
    (hBalance: (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let f:=markedVortexVertexEmbedding Q 0
      let g:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0
      let σ:=rawMarkedRestrictPair f g σglobal
      let H:=fun b x u=>Hglobal b (f x) (g u)
      let E:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) false
      let K:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) true
      let S:=Finset.univ.filter (fun s:W×Z=>H false s.1 s.2∨H true s.1 s.2)
      let I:=markedVortexInnerVertices Q 0
      let J:=markedVortexInnerHubs Q 0
      let T:=markedVortexDeeperVertices Q 0
      let R:=markedVortexDeeperHubs Q 0
      let bal:=markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4);
      ∃ errInner errDeep:ℝ, 0≤errDeep ∧
      errInner≤(x/2)*Fintype.card W ∧ errDeep≤(x/2)*Fintype.card W ∧
      (∀ v j,|bal I J v j|≤errInner) ∧
      (∀ v j,|bal T R v j|≤errDeep) ∧
      (∀ v j,|bal I J v j|≤etaBal*I.card)))
    (hCuts: ((∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q 0)=>fun y:↥(markedVortexInnerVertices Q 0)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q 0)) (markedVortexPermutation Q π hpres 0) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q 0)=>fun u:↥(markedVortexInnerHubs Q 0)=>
      Hglobal mark
        (markedVortexVertexEmbedding Q 0 x.val) (markedVortexHubEmbedding Q 0 u.val))) deltaI (2*hIcut))))
    (hBoundary: (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:=markedVortexNonDeeperHubToParent Q 0
      let X:=Finset.univ.image f
      let Zinner:=markedVortexInnerNonDeeperHubs Q 0
      let ω:=rawMarkedRestrictPair fP gP σglobal
      let H:=fun b x u=>Hglobal b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d h (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H)):
    MarkedVortexInitialRecordFields r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut :=by
  rcases hCommon with ⟨hc,h2,h3⟩
  rcases hDeep with ⟨hd,hl⟩
  rcases hActive with ⟨ha,h6⟩
  unfold MarkedVortexInitialRecordFields
  exact ⟨⟨hc,hd,ha⟩,h2,h3,⟨hl,hPotential⟩,hBalance,h6,hCuts,hBoundary⟩
end Oberwolfach
