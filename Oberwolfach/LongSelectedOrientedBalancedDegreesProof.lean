module

public import Oberwolfach.LongSelectedOrientedSourceBalancedDegrees
public import Oberwolfach.LongSelectedOrientedSourceHostComplement
public import Oberwolfach.LongSelectedOrientedSourceHostSpokes
public import Oberwolfach.LongSelectedOrientedSourceSpokes
public import Oberwolfach.LongSelectedOrientedSourceComplement
public import Oberwolfach.LongSelectedProtectedSourceComplement
public import Oberwolfach.LongSelectedProtectedSourceSpokes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longOrientedBalancedDegreesFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_oriented_balanced_degrees
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used DelG:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Sclass:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hphysical:∀x y,Mhost x y+Mhost y x=if Sclass.Adj x y then 1 else 0)
    (hbalance:∀v,(∑w,Mhost v w)=Fintype.card U ∧ (∑w,Mhost w v)=Fintype.card U):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedOrientedSourceWithHostSpokes hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ (fun x y=>Mhost x y=1) Extra ρ₀ θ δglobal M →
    LongSelectedOrientedSourceWithBalancedDegrees hU F P π d m ℓ raw t Jret σ H A Kbad Used DelG absorber δ Mhost Extra ρ₀ θ δglobal M :=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec0 : selectedOrientedHostSpokesFin n = longOrientedBalancedDegreesFin n := Subsingleton.elim _ _
  have hdec0K : selectedOrientedHostSpokesFin K = longOrientedBalancedDegreesFin K := Subsingleton.elim _ _
  have hdec1 : selectedOrientedBalancedDegreesFin n = longOrientedBalancedDegreesFin n := Subsingleton.elim _ _
  have hdec1K : selectedOrientedBalancedDegreesFin K = longOrientedBalancedDegreesFin K := Subsingleton.elim _ _
  try rw [hdec0] at hsource
  try rw [hdec0K] at hsource
  try rw [hdec1]
  try rw [hdec1K]
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,Φ,fC,hC,hR,hZ,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked⟩
  let extA:=fun w i=>ext w (.inl i)
  have hinnerA:∀w i p,inner w i p=extA w i ⟨p.val+2,by omega⟩:=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,hh,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩
    exact hh
  have hdisA:∀w i j,i≠j→Disjoint (Finset.univ.image (extA w i)) (Finset.univ.image (extA w j)):=by
    intro w i j hij
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_,_,_⟩
    exact hh (.inl i) (.inl j) (by simpa using hij)
  have hσ:∀w,(complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
      (bufferedFinalEndpoints (fun _=>(m+1)*d) (inner w))).image (factorCycleOrientation (F w) (E w))=
      complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
        (bufferedInitialEndpoints (fun _=>(m+1)*d) (inner w)):=by
    intro w
    simpa only [complementTailDomain,bufferedInitialEndpoints] using hsourceTail w
  have hbegin:∀w i,fC w (bufferedInitialEndpointInComplement (fun _=>(m+1)*d) (extA w) (inner w) (hinnerA w) (hdisA w) i)=i.val:=by
    intro w i
    exact hstart w i _
  have hend:∀w i,fC w (bufferedEndpointInComplement (fun _=>(m+1)*d) (extA w) (inner w) (hinnerA w) (hdisA w) i)=(π^d) i.val:=by
    intro w i
    exact hfinish w i _
  have hdegrees:=residual_degrees_from_retained_balanced_complement_explicit π (m+1) d (by omega) hnoshort
    (fun e=>raw (Sum.inr e)) false t Jret F hF E Dsrc hAlign extA inner hinnerA hdisA hσ fC hbegin hend
    Sclass Mhost hphysical hbalance hDirected hPacked
  exact ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hupper,hglobal,hcompletion,Φ,fC,hC,hR,hZ,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked,⟨hinnerA,hdisA,hσ,hdegrees⟩⟩
end Oberwolfach
