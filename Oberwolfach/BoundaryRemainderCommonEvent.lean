module

public import Oberwolfach.BoundaryAfterPacking
public import Oberwolfach.BoundaryIndexedSupports

@[expose] public section

/-! One boundary-edge event controls all later approximate packings and
coverings. Both the support changes and the selection bounds are computed
from their actual leftover and covering degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem boundary_remainder_selection_common_event (τ κ:ℝ)
    (hτ:0<τ) (hτ1:τ≤1) (hκ:0<κ) (hκ1:κ≤1) (q:ℕ):
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J],
      N≤Fintype.card V→∀ (G:SimpleGraph V) (A Z:Finset V) (x:J↪V),
      (∀ j,x j∈Z)→κ*Fintype.card V≤(A.card:ℝ)→
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ.le hτ1)).probability
          (fun σ=>∀ (C D G':SimpleGraph V),G'=(G\C)\D→
            Disjoint C (retainedGraph G σ)→∀ ℓ d:ℝ,0≤ℓ→0≤d→
            (∀ v,(((G\retainedGraph G σ)\C).degree v:ℝ)≤ℓ)→
            (∀ v,(D.degree v:ℝ)≤d)→ℓ+d≤τ^2*A.card/4→
            (∀ v,((changed (A∩(retainedGraph G σ).neighborFinset v)
              (A∩G'.neighborFinset v)).card:ℝ)≤ℓ+d) ∧
            (∀ i,((innerBoundarySupport G' A (x i)).card:ℝ)≤2*τ*Fintype.card A) ∧
            (∀ i j,i≠j→((innerBoundarySupport G' A (x i)∩innerBoundarySupport G' A (x j)).card:ℝ)≤
              (3*τ/κ)^2*Fintype.card A) ∧
            (∀ v:A,((Finset.univ.filter (fun i=>v∈innerBoundarySupport G' A (x i))).card:ℝ)≤
              (3*τ/κ)*Fintype.card A)):=by
  let ε:=τ^2*κ/4
  have hε:0<ε:=by dsimp [ε];positivity
  obtain ⟨N,hN⟩:=fresh_boundary_support_common_event ε hε q
  refine ⟨N,?_⟩
  intro V J _ _ _ _ hn G A Z x hx hsize
  have hevent:=hN V hn G A Z τ hτ.le hτ1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ C D G' hrem hCR ℓ d hℓ hd hleft hcover hsmall
  have hest:=boundary_after_packing_estimates G G (retainedGraph G σ) C D G' hrem A Z
    τ (ε*Fintype.card V) ℓ d (retainedGraph_le G σ) hCR hleft hcover
    (fun v=>(hσ.1 v).le) (fun v w hvw=>(hσ.2.1 v w hvw).le) (fun v hv=>(hσ.2.2 v hv).le)
  have hεsmall:ε*Fintype.card V≤τ^2*A.card/4:=by
    have hh:=mul_le_mul_of_nonneg_left hsize (show 0≤τ^2/4 by positivity)
    dsimp [ε];nlinarith only [hh]
  have herr:ε*Fintype.card V+2*(ℓ+d)≤τ^2*A.card:=by
    have ha:(0:ℝ)≤τ^2*A.card:=by positivity
    linarith
  refine ⟨?_,?_⟩
  · intro v
    have hh:=boundary_after_packing_support_change G (retainedGraph G σ) C D
      (retainedGraph_le G σ) hCR A v
    have he:changed (A∩(retainedGraph G σ).neighborFinset v) (A∩G'.neighborFinset v)=
        changed (A∩(retainedGraph G σ).neighborFinset v) (A∩((G\C)\D).neighborFinset v):=by
      ext w;simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,SimpleGraph.mem_neighborFinset,hrem]
    rw [he]
    have hh':((changed (A∩(retainedGraph G σ).neighborFinset v) (A∩((G\C)\D).neighborFinset v)).card:ℝ)≤
        ((G\retainedGraph G σ)\C).degree v+D.degree v:=by exact_mod_cast hh
    linarith [hleft v,hcover v]
  · apply boundary_indexed_selection_supports G G' A Z x hx τ κ
      (ε*Fintype.card V+2*(ℓ+d)) hτ.le hτ1 hκ hκ1 hsize herr
    · intro v;have hh:=hest.1 v;linarith
    · exact hest.2.1
    · intro v hv;have hh:=hest.2.2 v hv;linarith

end Oberwolfach
