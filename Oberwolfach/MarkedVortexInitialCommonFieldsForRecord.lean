module

public import Oberwolfach.MarkedVortexInitialCommonFromParentRecord
public import Oberwolfach.MarkedVortexInitialRecordFieldsOfTransfers

@[expose] public section
/-! Put the common transfer's statistics and cuts in the exact normal form
used by the initial-record assembly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_initial_common_fields_for_record
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut:ℝ)    (hpEq:p=initialIndexDensity U D*s₀/2) (hkEq:kval=p/((r+4:ℕ):ℝ))
    (hRaw:     let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hpres 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let c:ℝ:=(r+4:ℕ)
    let t:=s₀/c
    let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D;
    MarkedReferenceStatistics P ρ d a j Dload (κ/4) κ (2*(α/16)) p kval (c*t) t σ ∧
    MarkedReferenceCutFamilies P ρ d a j (2*(α/16)) p kval t σ ∧
    MarkedCommonConfigurationsWithSpokes r P ρ d βA (κ/4) σ H ∧
    MarkedRowsWithSpokes P ρ d (r+12) Finset.univ p kval (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W)):
    (let fP:=markedVortexVertexEmbedding Q 0
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
      MarkedReferenceCutFamilies (G.comap f) ρ d a j (2*(α/16)) pRef kRef t σ) :=by
  have hc:((r+4:ℕ):ℝ)≠0:=by positivity
  have hpRef:initialIndexDensity U D*((r+4:ℕ):ℝ)*(s₀/((r+4:ℕ):ℝ))/2=p:=by
    rw [hpEq];field_simp
  have hkRef:(initialIndexDensity U D*((r+4:ℕ):ℝ)*(s₀/((r+4:ℕ):ℝ))/2)/((r+4:ℕ):ℝ)=kval:=by
    rw [hpRef,hkEq]
  rcases hRaw with ⟨hstats,hcuts,hcommon,hrows,hindices,hrowdiff,hcoldiff⟩
  refine ⟨hcommon,⟨hrows,hindices,hrowdiff,hcoldiff⟩,?_⟩
  dsimp only
  rw [hkRef,hpRef]
  exact ⟨hstats,hcuts⟩
end Oberwolfach
