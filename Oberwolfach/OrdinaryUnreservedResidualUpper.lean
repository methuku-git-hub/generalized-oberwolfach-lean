module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.OrdinaryUnreservedFactorDensity
public import Oberwolfach.ResidualActualFullSelection

@[expose] public section
/-! The actual residual on the unreserved factor is small when the matched
cycle/path mass is nearly its exact source order and few approximate spoke
positions are missing. All errors are measured against the original order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_residual_upper
    {n r:ℕ} {K J:Type} [DecidableEq K] [DecidableEq J]
    (F:SimpleGraph (Fin n)) (C:Finset F.ConnectedComponent)
    (hsize:∀c:↥C,Fintype.card c.val=r) (rsv:ℝ) (hres:(r:ℝ)*C.card=rsv*n):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉C};
    ∀(a:ActualResidualData (K:=K) (J:=J) (F.induce S)) (ε κ:ℝ),
      (1-rsv-ε)*(n:ℝ)≤
        ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)+
          ((a.c*a.d-1:ℕ):ℝ)*(a.s₁.card+a.s₂.card)→
      (((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤κ*n→
      (a.remaining.card:ℝ)≤(ε+(a.c+1)*κ)*n:=by
  intro S a ε κ hmass hmissing
  have hh:=residual_actual_full_selection_comparison (F.induce S) a.s₁ a.s₂ a.hs a.u a.v a.P a.hp a.hP a.c a.d
    (by have h:=a.hc;omega) a.hd a.hlen a.T a.hT a.t a.root a.C a.hcross
  dsimp only at hh
  obtain ⟨q,hbase,hupper⟩ : ∃q:ℕ,
      q+(a.t.biUnion (fun j=>(a.C j).support.toFinset)).card+
        (a.c*a.d-1)*(a.s₁.card+a.s₂.card)=Fintype.card S ∧
      a.remaining.card≤q+(a.c+1)*(∑i∈a.s₂,(a.d-(a.T i).card)):=by
    refine ⟨_,hh.1,?_⟩
    change a.remaining.card≤_ 
    exact hh.2.2
  have hbaseR:=congrArg (fun x:ℕ=>(x:ℝ)) hbase
  push_cast at hbaseR
  have hupperR:(a.remaining.card:ℝ)≤(q:ℝ)+((a.c+1:ℕ):ℝ)*
      (((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ):=by exact_mod_cast hupper
  have hdensity:=ordinary_unreserved_factor_density F C hsize rsv hres
  change (Fintype.card S:ℝ)=(1-rsv)*n at hdensity
  have hm:((a.c+1:ℕ):ℝ)*(((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤
      ((a.c+1:ℕ):ℝ)*(κ*n):=mul_le_mul_of_nonneg_left hmissing (by positivity)
  push_cast at hupperR hm
  nlinarith
end Oberwolfach
