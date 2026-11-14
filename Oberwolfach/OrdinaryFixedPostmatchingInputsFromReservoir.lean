module

public import Oberwolfach.OrdinaryFixedReservoirSeparateListBudgets
public import Oberwolfach.OrdinaryFixedPostmatchingInputsFromEdit
public import Oberwolfach.OrdinaryFixedCorrectedReservoirLabelBudgets
public import Oberwolfach.OrdinaryCorrectedReservoirLabelBudgets
public import Oberwolfach.OrdinaryReservedActualTargetLists
public import Oberwolfach.OrdinaryReservedActualTargetAvoidance

@[expose] public section
/-! The same sample's corrected reservoir and selected reserved-list tests
supply actual edited-target deletion, assignment and list inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_postmatching_inputs_from_reservoir_eventually
    (r m t a bAbs d:ℕ) (lam bList bRate:ℝ) (hlam:0<lam) (hbList:0<bList) (hbRate:0<bRate):
    ∃N:ℕ,∀n:ℕ,N≤n→2≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P Target Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (A Z Wterm Inner:Finset (Fin n)) (Bterm B Hubs:Finset U) (ξ:ℝ)
    (γ pstar p smin rsv β ζ edit:ℝ) (s:U→Bool→ℝ)
    (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hsmin:0≤smin) (hs:smin≤rsv)
    (hseq:∀w,s w false=rsv) (hβ:0≤β) (hζ:0≤ζ) (hbζ:bList≤ζ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin)
    (hlistBudget:lam+2*ζ≤β)
    (hTests:OrdinaryReservedCompletionTests P π d p smin s σ)
    (Old:U→Finset (Fin n)) (hOld:∀u,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) (Old u)),
    let ε:ℝ:=min (lam/4) (bList/8)
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let F:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\F
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    (Inner.card:ℝ)≤ε*n→
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)→
    edit≤(bList/8)*n→
    ∀(K:Finset (Sym2 (Fin n)⊕(Fin n×U))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→U→Prop),
    OrdinaryCorrectedProtectedReservoirWitness r m t a bAbs ξ Reference F Href A Z Wterm Bterm B K JQ JH→
    let Ref0:=longPhysicalStateGraph P σ {0}\F
    let Protect0:=ordinaryMatchingProtect Ref0 Inner K
    let DelMatch:=Sample\Target
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    ∀{Kdim:ℕ} (mMatch:ℕ) (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
      (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin Kdim) (θ lamMatch aRow γrow:ℝ),
    OrdinarySelectedMatchingFamilyPostDemandResult F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π
      P DelMatch Target Protect0 F Inner bRate σ 0 J →
    OrdinaryFixedPostmatchingInputs F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Target σ Inner Hubs K lam bRate :=by
  obtain ⟨N,hbase⟩:=ordinary_fixed_reservoir_separate_list_budgets_eventually r m t a bAbs d lam bList bRate hlam hbList hbRate
  refine ⟨N,?_⟩
  intro n hn hn2 U _ _ P Target Host hHost π σ A Z Wterm Inner Bterm B Hubs ξ γ pstar p smin rsv β ζ edit s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests Old hOld ε Sample F Reference Href
    hInner hEdit hedit K JQ JH hW Ref0 Protect0 DelMatch J Kdim mMatch F₀ hF₀ Cres i₀ θ lamMatch aRow γrow hfamily
  have hh:=hbase n hn hn2 U P Target Host hHost π σ A Z Wterm Inner Bterm B Hubs ξ γ pstar p smin rsv β ζ edit s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests Old hOld hInner hEdit hedit K JQ JH hW
  obtain ⟨hsub,hlistSub,havoid,hcol,hfinish,hG,hsep,hGdeg,hDeldeg,hext,hlistOld⟩:=hh
  rw [ordinary_shared_sample_reference_graph_eq_state_zero P σ] at hext
  exact ordinary_fixed_postmatching_inputs_from_edit F₀ hF₀ Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Target σ Inner Hubs K lam bRate edit
    hEdit hsub havoid hcol hext hfamily
end Oberwolfach
