module

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

theorem ordinary_fixed_reservoir_separate_list_budgets_eventually
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
    let Abs:=ordinaryReservoirSpokeLabels K
    let Protect:=ordinaryMatchingProtect Reference Inner K
    let G:=ordinaryForbiddenRequired Target Sample Reference F Inner
    let Del:=ordinaryForbiddenSampleDeletion Sample Target Reference Protect F Inner
    let Lists:=fun u=>rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\(Inner∪Abs u)
    let T:=ordinaryInnerSpokeTargets Inner Hubs Href;
      (∀u,Abs u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ∧
      (∀u,Lists u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ∧
      (∀u,Disjoint (Lists u) (Abs u) ∧ Disjoint (T u) (Abs u) ∧ T u⊆Inner ∧ (T u≠∅→u∈Hubs)) ∧
      (∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤bRate*n) ∧
      Sample\(Target\Protect)≤Del ∧ G≤Target\Protect ∧
      (∀x y,G.Adj x y→¬(Sample\Del).Adj x y) ∧
      (∀v,(G.degree v:ℝ)≤bList*n) ∧ (∀v,(Del.degree v:ℝ)≤bList*n) ∧
      (∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y) (Lists u) (lam/2)) ∧
      (∀u,Disjoint (Lists u) (Old u)) :=by
  let ε:ℝ:=min (lam/4) (bList/8)
  have hε:ε≤lam/4:=min_le_left _ _
  have hεb:ε≤bList/8:=min_le_right _ _
  obtain ⟨Nr,hr⟩:=ordinary_fixed_corrected_reservoir_label_budgets_eventually r m t a bAbs lam ε bRate hlam hε hbRate
  obtain ⟨Nrow,hrow⟩:=ordinary_constant_eventually_below_linear_rate (bList/8) (2^(t*t)*a) (by positivity)
  obtain ⟨Nconf,hNconf⟩:=ordinary_constant_eventually_below_linear_rate (bList/8) (2*((3*d:ℕ):ℝ)) (by positivity)
  refine ⟨max Nr (max Nrow Nconf),?_⟩
  intro n hn hn2 U _ _ P Target Host hHost π σ A Z Wterm Inner Bterm B Hubs ξ γ pstar p smin rsv β ζ edit s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests Old hOld ε' Sample F Reference Href hInner hEdit hedit K JQ JH hW
  have hInner':(Inner.card:ℝ)≤ε*n:=by simpa only [ε] using hInner
  obtain ⟨hsub,htrim,hcol⟩:=hr n (by omega) U π d σ ξ Reference F A Z Wterm Inner Bterm B hInner' K JQ JH hW
  let Abs:=ordinaryReservoirSpokeLabels K
  have havoid:=ordinary_reserved_actual_target_avoidance π d σ Inner Hubs Abs hsub
  have hn0:(0:ℝ)≤n:=by positivity
  have hrows:((ordinaryResourceRows K).card:ℝ)≤(bList/8)*n:=by
    have hh:((ordinaryResourceRows K).card:ℝ)≤((2^(t*t)*a:ℕ):ℝ):=by exact_mod_cast hW.2.2.1
    have hconst:((2^(t*t)*a:ℕ):ℝ)≤(bList/8)*n:=by
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hrow n (by omega)
    exact hh.trans hconst
  have hInnerB:(Inner.card:ℝ)≤(bList/8)*n:=hInner'.trans (mul_le_mul_of_nonneg_right hεb hn0)
  have hbudget:(lam+2*bList)*n≤β*n:=by
    have hh:lam+2*bList≤β:=by linarith
    exact mul_le_mul_of_nonneg_right hh hn0
  have hconf:2*((3*d:ℕ):ℝ)≤(bList/8)*n:=hNconf n (by omega)
  have htarget:=ordinary_reserved_actual_target_lists hn2 P Target Host hHost π d σ Inner Hubs K Abs Old
    γ pstar p smin rsv β lam bList (lam/2) edit s hγ hpstar hp hsmin hs hseq hβ hlam.le hbList.le (by positivity)
    hP herror hmargin hbudget hTests htrim hOld
  have hBound:edit+2*Inner.card+(ordinaryResourceRows K).card+2*((3*d:ℕ):ℝ)≤bList*n:=by
    nlinarith [hedit,hInnerB,hrows,hconf]
  have hh:=htarget hEdit hBound
  refine ⟨hsub,?_,?_,hcol,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2⟩
  · intro u;exact (havoid u).1
  · intro u;exact (havoid u).2
end Oberwolfach
