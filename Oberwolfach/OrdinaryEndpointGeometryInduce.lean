module

public import Oberwolfach.OrdinaryInducedEndpointCounts

@[expose] public section
/-! Ambient endpoint size, row, column and codegree estimates transfer
unchanged to the induced physical domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W K:Type} [Fintype W] [Fintype K] [DecidableEq W] [DecidableEq K]

theorem ordinary_endpoint_geometry_induce
    (G F:SimpleGraph W) (T:Finset W) (S R:K→Finset W) (t:K→ℝ) (a η:ℝ)
    (hST:∀k,S k⊆T) (hRT:∀k,R k⊆T)
    (hsize:∀k,a*T.card≤((S k).card:ℝ) ∧ a*T.card≤((R k).card:ℝ))
    (hrow:∀k v,v∈S k→|(((R k)∩G.neighborFinset v).card:ℝ)-t k*(R k).card|≤η*(R k).card)
    (hcol:∀k v,v∈R k→|(((S k)∩G.neighborFinset v).card:ℝ)-t k*(S k).card|≤η*(S k).card)
    (hcodeg:∀k v,v∈S k→∀w,w∈S k→v≠w→¬F.Adj v w→
      ((((R k)∩G.neighborFinset v)∩G.neighborFinset w).card:ℝ)≤(t k^2+η)*(R k).card):
    (∀k,a*Fintype.card {v:W // v∈T}≤((ordinaryInducedFinset T (S k)).card:ℝ) ∧
      a*Fintype.card {v:W // v∈T}≤((ordinaryInducedFinset T (R k)).card:ℝ)) ∧
    (∀k (v:{v:W // v∈T}),v∈ordinaryInducedFinset T (S k)→
      |(((ordinaryInducedFinset T (R k)∩(G.induce (T:Set W)).neighborFinset v).card:ℝ)-
        t k*(ordinaryInducedFinset T (R k)).card)|≤η*(ordinaryInducedFinset T (R k)).card) ∧
    (∀k (v:{v:W // v∈T}),v∈ordinaryInducedFinset T (R k)→
      |(((ordinaryInducedFinset T (S k)∩(G.induce (T:Set W)).neighborFinset v).card:ℝ)-
        t k*(ordinaryInducedFinset T (S k)).card)|≤η*(ordinaryInducedFinset T (S k)).card) ∧
    (∀k (v:{v:W // v∈T}),v∈ordinaryInducedFinset T (S k)→∀w,w∈ordinaryInducedFinset T (S k)→
      v≠w→¬(F.induce (T:Set W)).Adj v w→
      (((ordinaryInducedFinset T (R k)∩(G.induce (T:Set W)).neighborFinset v)∩
        (G.induce (T:Set W)).neighborFinset w).card:ℝ)≤(t k^2+η)*(ordinaryInducedFinset T (R k)).card):=by
  have hc:Fintype.card {v:W // v∈T}=T.card:=by simp
  refine ⟨?_,?_,?_,?_⟩
  · intro k
    rw [hc,ordinary_induced_finset_card T (S k) (hST k),ordinary_induced_finset_card T (R k) (hRT k)]
    exact hsize k
  · intro k v hv
    have hv':v.val∈S k:=by simpa [ordinaryInducedFinset] using hv
    rw [ordinary_induced_endpoint_neighbor_card G T (R k) (hRT k) v,
      ordinary_induced_finset_card T (R k) (hRT k)]
    exact hrow k v.val hv'
  · intro k v hv
    have hv':v.val∈R k:=by simpa [ordinaryInducedFinset] using hv
    rw [ordinary_induced_endpoint_neighbor_card G T (S k) (hST k) v,
      ordinary_induced_finset_card T (S k) (hST k)]
    exact hcol k v.val hv'
  · intro k v hv w hw hne hfree
    have hv':v.val∈S k:=by simpa [ordinaryInducedFinset] using hv
    have hw':w.val∈S k:=by simpa [ordinaryInducedFinset] using hw
    have hn:v.val≠w.val:=fun hh=>hne (Subtype.ext hh)
    have hf:¬F.Adj v.val w.val:=hfree
    rw [ordinary_induced_endpoint_codegree_card G T (R k) (hRT k) v w,
      ordinary_induced_finset_card T (R k) (hRT k)]
    exact hcodeg k v.val hv' w.val hw' hn hf
end Oberwolfach
