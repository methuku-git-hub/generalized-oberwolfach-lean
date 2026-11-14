module

public import Oberwolfach.OrdinaryReservedCompletionTests
public import Oberwolfach.ReservedSpokeTrimmedLists

@[expose] public section
/-! The same selected reserved-completion tests give lists uniformly after
small physical deletions and after removing inner and absorber labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_trimmed_lists_from_tests
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:2≤n)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (γ pstar p smin rsv β lam ζ lamFinal:ℝ) (s:U→Bool→ℝ)
    (hγ:0≤γ) (hpstar:0≤pstar) (hp:pstar≤p) (hsmin:0≤smin) (hs:smin≤rsv)
    (hseq:∀w,s w false=rsv) (hβ:0≤β) (hlam:0≤lam) (hζ:0≤ζ) (hlamFinal:0≤lamFinal)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ))
    (herror:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n)
    (hmargin:β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin)
    (hbudget:(lam+2*ζ)*n≤β*n)
    (hTests:OrdinaryReservedCompletionTests P π d p smin s σ)
    (Inner:Finset (Fin n)) (Abs Old:U→Finset (Fin n))
    (htrim:∀u,lamFinal*n+Inner.card+(Abs u).card≤lam*n)
    (hOld:∀u,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) (Old u)):
    ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζ*n)→
      (∀u,IsExtendingList
        (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y)
        (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\(Inner∪Abs u)) lamFinal) ∧
      (∀u,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\(Inner∪Abs u)) (Old u)) :=by
  intro Del hDel
  have hnb:∀u i,|rawIntervalReservedLabelHubCountOn π d (fun e=>σ (Sum.inr e)) u false
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i).card*rsv|<(n:ℝ)^(3/4:ℝ):=by
    intro u i
    simpa only [hseq u] using hTests.2.1 u i
  have hpaths:=hTests.1
  have hdec:ordinaryReservedSpokeExtendingFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [←hdec] at hpaths hnb
  have hext:=ordinary_reserved_spoke_extending_lists hn P π d σ γ pstar p smin rsv β lam ζ
    hγ hpstar hp hsmin hs hβ hlam hζ hP herror hpaths hnb hmargin hbudget Del hDel
  rw [hdec] at hext
  exact reserved_spoke_trimmed_lists π d (fun e=>σ (Sum.inr e)) _ Inner Abs Old lam lamFinal hlamFinal
    (by simpa only [Fintype.card_fin] using htrim) hext hOld
end Oberwolfach
