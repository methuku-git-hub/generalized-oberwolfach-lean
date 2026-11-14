module

public import Oberwolfach.MarkedVortexPositiveRecordConsequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_positive_record_consequences_transfer
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut:ℝ)
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κ thetaDeep etaBal x eta deltaI hIcut)
    (hEq:∀i≤L,1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σold=
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σglobal ∧
      (fun b x u=>Hold b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))=
        (fun b x u=>Hglobal b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))):
    MarkedVortexPositiveRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal βA βrec κ thetaDeep etaBal x eta deltaI hIcut :=by
  unfold MarkedVortexCorrectedRecordConsequences at hOld
  unfold MarkedVortexPositiveRecordConsequences
  rcases hOld with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h1 i hi
    simpa only [←hs,hhpoint,←hh] using h
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h2 i hi
    simpa only [←hs,hhpoint,←hh] using h
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h3 i hi
    simpa only [←hs,hhpoint,←hh] using h
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h4 i hi
    simpa only [←hs,hhpoint,←hh] using h
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h5 i hi
    dsimp only
    rw [←hs]
    simpa only [hhpoint,←hh] using h
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h6 i hi
    simpa only [←hs,hhpoint,←hh] using h
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h7 i hi
    simpa only [←hs,hhpoint,←hh] using h
  · intro i hi hpos
    obtain ⟨hs,hh⟩:=hEq i hi hpos
    have hhpoint : ∀ b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i),
        Hglobal b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u)=
          Hold b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u) := by
      intro b v u
      exact (congrFun (congrFun (congrFun hh b) v) u).symm
    have h:=h8 i hi
    simpa only [←hs,hhpoint,←hh] using h
end Oberwolfach
