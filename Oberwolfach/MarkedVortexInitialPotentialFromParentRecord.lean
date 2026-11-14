module

public import Oberwolfach.MarkedVortexInitialPotentialTransfer
public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section
/-! Transfer all initial potential roots directly from the original parent
record, preserving its weight and its nonzero-marginal restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_potential_from_parent_record
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [Nonempty V] [DecidableEq U]
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (βA βrec κold thetaDeep etaBal x eta deltaI hIcut:ℝ)
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κold thetaDeep etaBal x eta deltaI hIcut)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (ζ κ B pstar A:ℝ)
    (hζ:0≤ζ) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (hinterval:∀e,σold (Sum.inr e)=σglobal (Sum.inr e))
    (hR:∀e,¬(rawMarkedPairRims G π d σold e↔rawMarkedPairRims G π d σglobal e)→markedPairPhysical π e∈FR.edgeFinset)
    (hS:∀b v u,¬(Hold b v u↔Hglobal b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V):
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let P:=G.comap (markedVortexVertexEmbedding Q 0)
    let ρ:=markedVortexPermutation Q π hpres 0
    let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
    let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal
    let H:=fun b v u=>Hglobal b (markedVortexVertexEmbedding Q 0 v) (markedVortexHubEmbedding Q 0 u)
    let qi:=fun u=>q (markedVortexHubEmbedding Q 0 u)
    let si:=fun u=>s (markedVortexHubEmbedding Q 0 u);
    0≤B→(Fintype.card W:ℝ)/2≤Dload→Dload≤2*Fintype.card W→
    0<pstar→pstar≤p→pstar≤kval→pstar≤s₀→p≤1→kval≤1→s₀≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) Dload τParent A B (weightParent 0)→
    κold/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤κ/4→
    let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd (r+4) ρ (3*d)
      (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weightParent 0 X.1.val/(Dload*p^(r+4)*kval*s₀^(r+4));
    ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
      rawMarkedWheelMarginal P ρ d p kval qi si a j root≠0→
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1|≤κ/4 :=by
  intro W Z P ρ Dload σ H qi si hB hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 hw hbudget seed root hmarginal
  unfold MarkedVortexCorrectedRecordConsequences at hOld
  obtain ⟨_,_,_,hpotential,_,_,_,_⟩:=hOld
  obtain ⟨_,hpot⟩:=hpotential 0 (Nat.zero_le L)
  have htransfer:=marked_vortex_initial_potential_transfer V U Γ Color G D m β ε Q π hpres d (r+4) (by omega) hn hu
    σold σglobal Hold Hglobal FR FS ζ hζ hinterval hR hS hFR hFS Dload τParent A B p kval s₀ pstar (κold/4)
    hB hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 (weightParent 0) hw root (hpot root hmarginal)
  apply htransfer.trans
  convert hbudget using 1 <;> push_cast <;> ring
end Oberwolfach
