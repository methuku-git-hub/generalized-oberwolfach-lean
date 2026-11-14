module

public import Oberwolfach.LongReferenceResidualChangeGraphOnRoots
public import Oberwolfach.LongReferenceResidualDirectedChanges

@[expose] public section
/-! The corrected full residual has a raw encoding on the same sample, and
all directed rim changes are charged to a bounded physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance encodedReferenceOnRootsDecEq : DecidableEq V := Classical.decEq V
local instance encodedReferenceOnRootsArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_encoded_residual_reference_change_on_roots
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (I:Finset V) (η δ χ:ℝ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hhost:∀x y,M x y=1→G.Adj x y)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hI:∀v,π v∈I↔v∈I) (Roots:Finset V) (ηLocal δLocal χLocal:ℝ):
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e);
    ∀T:Finset {e:V×V // P e},
    (∀e∈T,longMarkedArcEligible π d e.val)→(∀e,e∉T→longOrdinaryArcEligible π d e.val)→
    (∀mark x y,x∈I→y∈I→
      (markedPhysicalRim G π (3*d) (fun e=>raw (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y))→
    (∀x,((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset x) ((S\Small).neighborFinset x)).card:ℝ)≤η)→
    (∀x,(Del.degree x:ℝ)≤δ)→
    (∀x,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree x:ℝ)≤χ)→
    (∀x∈Roots,((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset x) ((S\Small).neighborFinset x)).card:ℝ)≤ηLocal)→
    (∀x∈Roots,(Del.degree x:ℝ)≤δLocal)→
    (∀x∈Roots,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree x:ℝ)≤χLocal)→
    ∃(τ:RawMarkedOutcome V U Γ Color) (FR:SimpleGraph V),
      (∀e,τ (Sum.inr e)=raw (Sum.inr e)) ∧
      (∀e:Sym2 V,e.toFinset⊆I→τ (Sum.inl e)=raw (Sum.inl e)) ∧
      (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y) ∧
      (∀a,¬(rawMarkedPairRims G π d raw a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset) ∧
      (∀x,(FR.degree x:ℝ)≤η+δ+χ) ∧
      (∀x∈Roots,(FR.degree x:ℝ)≤ηLocal+δLocal+χLocal):=by
  intro P T₁ raw T hMarked hOrd hInner hChange hDel hRetype hChangeLocal hDelLocal hRetypeLocal
  let E:=residualOrdinaryArc P T
  let K:=residualMarkedArc P T
  let tail:=fun e:E=>e.val.val.1
  let head:=fun e:E=>e.val.val.2
  let ktail:=fun e:K=>e.val.val.1
  let khead:=fun e:K=>π.symm e.val.val.2
  let τ:=rawMarkedEncodeHost tail head ktail khead π raw I
  let FR:=longReferenceResidualChangeGraph (longSelectedPhysicalGraph G π d ω) (S\Small) Del (physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁))
  have henc:=long_dual_residual_raw_encoding G S Small π d M hphysical hhost raw I hI T hMarked hOrd hInner
  refine ⟨τ,FR,henc.1,henc.2.1,henc.2.2,?_,?_,?_⟩
  · exact long_reference_residual_directed_changes G S Del Small π d ω M τ hphysical hcorrect T henc.2.2
  · have hb:=long_reference_residual_change_graph_degree (longSelectedPhysicalGraph G π d ω) (S\Small) Del
        (physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)) η δ χ
        (by intro x; convert hChange x using 1 <;> congr!) hDel
        (by intro x; convert hRetype x using 1 <;> congr!)
    intro x
    convert hb x using 1 <;> congr!
  · have hb:=long_reference_residual_change_graph_degree_on_roots (longSelectedPhysicalGraph G π d ω) (S\Small) Del
        (physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)) Roots ηLocal δLocal χLocal
        (by intro x hx; convert hChangeLocal x hx using 1 <;> congr!) hDelLocal
        (by intro x hx; convert hRetypeLocal x hx using 1 <;> congr!)
    intro x hx
    convert hb x hx using 1 <;> congr!
end Oberwolfach
