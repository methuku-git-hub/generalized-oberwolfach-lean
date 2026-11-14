module

public import Oberwolfach.OrdinaryUnreservedMatchingResidualUpper
public import Oberwolfach.OrdinaryResidualMissingPacked

@[expose] public section
/-! Bound the unreserved residual directly from the matched-cycle mass and
the uncovered marked-spoke count on the same sampled wheel family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_packed_matching_residual_upper
    {n r:ℕ} {U A J E L:Type} [Fintype U] [DecidableEq U] [DecidableEq A] [Fintype J] [DecidableEq J]
    [Fintype E] [Fintype L]
    (F:SimpleGraph (Fin n)) (C:Finset F.ConnectedComponent)
    (hsize:∀c:↥C,Fintype.card c.val=r) (rsv:ℝ) (hres:(r:ℝ)*C.card=rsv*n)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (u:U)
    (tail head:E→Fin n) (ktail khead:L→Fin n) (H₀ Hₖ:Fin n→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π (3*d) H₀ Hₖ)):
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true}
    let S:Set (Fin n):={x | F.connectedComponentMk x∉C};
    ∀(a:ActualResidualData (K:=A⊕B) (J:=J) (F.induce S)) (len:J→ℕ),
      a.d=d→a.s₂=secondSumIndices→a.t=Finset.univ→
      a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset)→
      (∀j,(a.C j).length=len j)→
      (∀b:B,a.T (.inr b)=packedPhysicalSpokePositions tail head ktail khead m (3*d) d π H₀ Hₖ M u b.val)→
    ∀ε κ:ℝ,
      (1-rsv-ε)*(n:ℝ)≤((∑j,len j):ℝ)+
        ((a.c*a.d-1:ℕ):ℝ)*(a.s₁.card+a.s₂.card)→
    let Covered:=Finset.univ.filter (fun v=>∃W∈M,Sum.inr (v,u)∈markedWheelPhysicalResources W);
      (((Finset.univ.filter (fun v=>rawMarkedSpokes π d (fun e=>raw (Sum.inr e)) true true true v u))\Covered).card:ℝ)≤κ*n→
      (a.remaining.card:ℝ)≤(ε+(a.c+1)*κ)*n:=by
  intro B S a len hd' hs ht hEmbed hlen hpositions ε κ hmass Covered huncov
  have hmiss:=ordinary_residual_missing_from_packed (A:=A) (J:=J) π d m hd hnoshort raw t Jret u tail head ktail khead H₀ Hₖ M a hd' hs hpositions
  have hmissR:(((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤κ*n:=
    (show (((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤
      (((Finset.univ.filter (fun v=>rawMarkedSpokes π d (fun e=>raw (Sum.inr e)) true true true v u))\Covered).card:ℝ) by exact_mod_cast hmiss).trans huncov
  exact ordinary_unreserved_matching_residual_upper F C hsize rsv hres a len ht hEmbed hlen ε κ hmass hmissR
end Oberwolfach
