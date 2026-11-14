module

public import Oberwolfach.CompleteWalkIntervalExtension
public import Oberwolfach.MarkedDirectedWheelInterval

@[expose] public section
/-! Concatenate only the selected marked-wheel rims into a directed run;
no wheel is required outside the selected interval. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_marked_wheel_directed_run
    {V:Type*} (v:ℕ → V) (c n start:ℕ) (hne:∀ i,v i≠v (i+1))
    (C:ℕ → Fin c → V)
    (p:∀ i, start ≤ i  →  i < start+n  →  (SimpleGraph.completeGraph V).Walk (v i) (v (i+1)))
    (hp:∀ i (hi:start ≤ i) (hj:i < start+n),(p i hi hj).IsPath)
    (hlen:∀ i (hi:start ≤ i) (hj:i < start+n),(p i hi hj).length=c)
    (hsupport:∀ i (hi:start ≤ i) (hj:i < start+n),(p i hi hj).support.dropLast=List.ofFn (C i))
    (hdis:∀ i j, start ≤ i  →  i < start+n  →  start ≤ j  →  j < start+n  →  i ≠ j  →  ∀ a b:Fin c, C i a ≠ C j b)
    (hend:∀ i, start ≤ i  →  i < start+n  →  ∀ a:Fin c, v (start+n) ≠ C i a)
    (R:V → V → Prop)
    (hR:∀ i (hi:start ≤ i) (hj:i < start+n) k,k<(p i hi hj).length → R ((p i hi hj).getVert k) ((p i hi hj).getVert (k+1))):
    ∃q:(SimpleGraph.completeGraph V).Walk (v start) (v (start+n)),q.IsPath ∧ q.length=n*c ∧
      (∀x,x∈q.support ↔ x=v (start+n) ∨
        ∃i,start ≤ i ∧ i < start+n ∧ ∃a:Fin c,C i a=x) ∧
      (∀ j,j≤n → q.getVert (c*j)=v (start+j)) ∧
      (∀ k,k<q.length → R (q.getVert k) (q.getVert (k+1))):=by
  obtain ⟨p',hmatch⟩:=complete_graph_extend_interval_walks v start n hne p
  apply marked_wheel_directed_interval_from_rim_supports (SimpleGraph.completeGraph V) v c n start C p'
  · intro i hi hj;rw [hmatch i hi hj];exact hp i hi hj
  · intro i hi hj;rw [hmatch i hi hj];exact hlen i hi hj
  · intro i hi hj;rw [hmatch i hi hj];exact hsupport i hi hj
  · exact hdis
  · exact hend
  · intro i hi hj k hk
    rw [hmatch i hi hj] at hk ⊢
    exact hR i hi hj k hk
end Oberwolfach
