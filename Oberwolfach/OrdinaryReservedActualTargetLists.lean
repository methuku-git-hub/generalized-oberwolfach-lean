module

public import Oberwolfach.OrdinaryActualSelectedListsOnTarget
public import Oberwolfach.OrdinaryReservedListsFromTests

@[expose] public section
/-! The reserved selected lists remain extending in the exact edited target,
after the deletion chosen from the sample and protected reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_actual_target_lists
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:2≤n)
    (P Target Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (K:Finset (Sym2 (Fin n) ⊕ (Fin n×U)))
    (Abs Old:U→Finset (Fin n))
    (γ pstar p smin rsv β lam ζ lamFinal edit:ℝ) (s:U→Bool→ℝ)
    (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hsmin:0≤smin) (hs:smin≤rsv)
    (hseq:∀w,s w false=rsv) (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ) (hlamFinal:0≤lamFinal)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin)
    (hlistBudget:(lam+2*ζ)*n≤β*n)
    (hTests:OrdinaryReservedCompletionTests P π d p smin s σ)
    (htrim:∀u,lamFinal*n+Inner.card+(Abs u).card≤lam*n)
    (hOld:∀u,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) (Old u)):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let F:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\F
    let Protect:=ordinaryMatchingProtect Reference Inner K
    let G:=ordinaryForbiddenRequired Target Sample Reference F Inner
    let Del:=ordinaryForbiddenSampleDeletion Sample Target Reference Protect F Inner
    let Lists:=fun u=>rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\(Inner∪Abs u);
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)→
    edit+2*Inner.card+(ordinaryResourceRows K).card+2*((3*d:ℕ):ℝ)≤ζ*n→
    Sample\(Target\Protect)≤Del ∧ G≤Target\Protect ∧
    (∀x y,G.Adj x y→¬(Sample\Del).Adj x y) ∧
    (∀v,(G.degree v:ℝ)≤ζ*n) ∧ (∀v,(Del.degree v:ℝ)≤ζ*n) ∧
    (∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y) (Lists u) lamFinal) ∧
    (∀u,Disjoint (Lists u) (Old u)) :=by
  intro Sample F Reference Protect G Del Lists hEdit hBudget
  have hLists:∀Del':SimpleGraph (Fin n),(∀x,(Del'.degree x:ℝ)≤ζ*n)→∀u,
      IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del'.Adj x y) (Lists u) lamFinal:=by
    intro Del' hDel'
    exact (ordinary_reserved_trimmed_lists_from_tests hn P π d σ γ pstar p smin rsv β lam ζ lamFinal s
      hγ hpstar hp hsmin hs hseq hβ hlam hζ hlamFinal hP herror hmargin hlistBudget hTests Inner Abs Old htrim hOld Del' hDel').1
  have hh:=ordinary_actual_selected_lists_on_target P Target Host hHost π d σ Inner Hubs K edit ζ lamFinal Lists hEdit hBudget hLists
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2,?_⟩
  intro u
  exact (hOld u).mono_left Finset.sdiff_subset
end Oberwolfach
