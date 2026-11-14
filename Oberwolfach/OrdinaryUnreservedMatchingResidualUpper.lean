module

public import Oberwolfach.OrdinaryUnreservedResidualUpper
public import Oberwolfach.ResidualActualCycleMass

@[expose] public section
/-! Express the residual upper bound directly through the sizes of the
matched source cycles, allowing those sizes to be supplied by the matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_matching_residual_upper
    {n r:ℕ} {K J:Type} [DecidableEq K] [Fintype J] [DecidableEq J]
    (F:SimpleGraph (Fin n)) (C:Finset F.ConnectedComponent)
    (hsize:∀c:↥C,Fintype.card c.val=r) (rsv:ℝ) (hres:(r:ℝ)*C.card=rsv*n):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉C};
    ∀(a:ActualResidualData (K:=K) (J:=J) (F.induce S)) (len:J→ℕ),
      a.t=Finset.univ→a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset)→
      (∀j,(a.C j).length=len j)→∀ε κ:ℝ,
      (1-rsv-ε)*(n:ℝ)≤((∑j,len j):ℝ)+
          ((a.c*a.d-1:ℕ):ℝ)*(a.s₁.card+a.s₂.card)→
      (((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤κ*n→
      (a.remaining.card:ℝ)≤(ε+(a.c+1)*κ)*n:=by
  intro S a len ht hEmbed hlen ε κ hmass hmissing
  have hcycle:(a.t.biUnion (fun j=>(a.C j).support.toFinset)).card=∑j,len j:=by
    calc
      _ = a.Cembed.card:=congrArg Finset.card hEmbed.symm
      _ = ∑j,(a.C j).length:=actual_residual_cycle_mass a ht hEmbed
      _ = ∑j,len j:=by apply Finset.sum_congr rfl;intro j _;exact hlen j
  apply ordinary_unreserved_residual_upper F C hsize rsv hres a ε κ
  · rw [hcycle]
    simpa only [Nat.cast_sum] using hmass
  · exact hmissing
end Oberwolfach
