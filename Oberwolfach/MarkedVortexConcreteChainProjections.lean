module

public import Oberwolfach.MarkedVortexConcreteReferenceChain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_concrete_reference_chain_projections
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ) (N NI Kgeom:ℕ)
    (hd:1≤d) (he:0≤ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u a=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u j=s₀)
    (hXi0:0≤xiDeep) (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep≤κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep≤(s₀/(((r+4):ℕ):ℝ))*ω/32)
    (hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i))
    (hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i))
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (hRec:MarkedVortexParentRecordConsequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z βA βrec κ thetaDeep etaBal x eta deltaI hIcut)
:
  let hc:0<L+1:=by omega
  let R:=fun i:Fin (L+1)=>marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec i.val (by omega)
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  let C:=markedVortexConcreteReferenceChain r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec;
  (∀ (i:Fin (L+1)) v,markedVortexVertexEmbedding Q 0 (C.intoV i v)=markedVortexVertexEmbedding Q i.val v) ∧
  (∀ (i:Fin (L+1)) u,markedVortexHubEmbedding Q 0 (C.intoU i u)=markedVortexHubEmbedding Q i.val u) := by
  constructor <;> intro i v <;> rfl
end Oberwolfach
