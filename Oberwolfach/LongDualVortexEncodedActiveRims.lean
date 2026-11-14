module

public import Oberwolfach.LongDualResidualRawEncoding
public import Oberwolfach.MarkedVortexFirstActiveExactRims
public import Oberwolfach.LongEncodedResidualSampleDivisibility

@[expose] public section
/-! The balanced residual has one encoding which preserves the selected
sample on the first active set, and transfers its exact divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
local instance dualVortexEncodingDecEq {V:Type}:DecidableEq V:=Classical.decEq _
local instance dualVortexEncodingArc {V:Type} (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_dual_vortex_encoded_active_rims
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (G S Small:SimpleGraph V) (D mm:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε mm)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d m:ℕ) (Mhost:V→V→ℕ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hhost:∀x y,Mhost x y=1→G.Adj x y)
    (raw:RawMarkedOutcome V U Γ Color)
    (T:Finset {e:V×V // longEligibleResidualArc Mhost Small ⊥ e})
    (hMarked:∀e∈T,longMarkedArcEligible π d e.val)
    (hOrd:∀e,e∉T→longOrdinaryArcEligible π d e.val)
    (hInner:∀mark x y,x∈Q.extendedVertices 1→y∈Q.extendedVertices 1→
      (markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧e.val.val.2=y))
    (HK:V→U→Prop) (Sp:Finset (V×U))
    (hdiv:MarkedRemainderDivisible
      (fun e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      HK Finset.univ Sp m):
    ∃τ:RawMarkedOutcome V U Γ Color,
      (∀e,τ (Sum.inr e)=raw (Sum.inr e)) ∧
      (∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→τ (Sum.inl e)=raw (Sum.inl e)) ∧
      (let f:=markedVortexActiveVertexEmbedding Q 1
       let g:=markedVortexNonDeeperHubToPhysical Q 0
       let ρ:=markedVortexActivePermutation Q π hπ 1;
       rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g τ)=
       rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g raw)) ∧
      (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc (longEligibleResidualArc Mhost Small ⊥) T,e.val.val.1=x∧e.val.val.2=y) ∧
      MarkedRemainderDivisible
        (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc G π (3*d) (fun e=>τ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        HK Finset.univ Sp m :=by
  let P:=longEligibleResidualArc Mhost Small ⊥
  let E:=residualOrdinaryArc P T
  let K:=residualMarkedArc P T
  let tail:=fun e:E=>e.val.val.1
  let head:=fun e:E=>e.val.val.2
  let ktail:=fun e:K=>e.val.val.1
  let khead:=fun e:K=>π.symm e.val.val.2
  let τ:=rawMarkedEncodeHost tail head ktail khead π raw (Q.extendedVertices 1)
  have henc:=long_dual_residual_raw_encoding G S Small π d Mhost hphysical hhost raw (Q.extendedVertices 1) (hπ 1) T hMarked hOrd hInner
  refine ⟨τ,henc.1,henc.2.1,?_,henc.2.2,?_⟩
  · exact marked_vortex_first_active_exact_rims G D mm β ε Q π hπ d raw τ henc.2.1
  · exact long_encoded_residual_sample_divisibility G S Small Mhost π d m (fun e=>τ (Sum.inl e)) T HK Sp henc.2.2 hdiv
end Oberwolfach
