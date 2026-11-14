module

public import Oberwolfach.CompleteWalkIntervalExtension
public import Oberwolfach.MarkedDirectedWheelIntervalEdges

@[expose] public section
/-! Concatenate only the selected marked-wheel rims into a directed run;
no wheel is required outside the selected interval. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_marked_wheel_directed_run_with_edges
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
      (∀e:Sym2 V,e∈q.edges ↔ ∃ i, ∃ hi:start ≤ i, ∃ hj:i < start+n, e∈(p i hi hj).edges) ∧
      (∀ k,k<q.length → R (q.getVert k) (q.getVert (k+1))):=by
  obtain ⟨p',hmatch⟩:=complete_graph_extend_interval_walks v start n hne p
  have hp':∀ i, start ≤ i → i < start+n → (p' i).IsPath:=by
    intro i hi hj;rw [hmatch i hi hj];exact hp i hi hj
  have hl':∀ i, start ≤ i → i < start+n → (p' i).length=c:=by
    intro i hi hj;rw [hmatch i hi hj];exact hlen i hi hj
  have hs':∀ i, start ≤ i → i < start+n → (p' i).support.dropLast=List.ofFn (C i):=by
    intro i hi hj;rw [hmatch i hi hj];exact hsupport i hi hj
  have hr':∀ i, start ≤ i → i < start+n → ∀ k, k < (p' i).length→R ((p' i).getVert k) ((p' i).getVert (k+1)):=by
    intro i hi hj k hk
    rw [hmatch i hi hj] at hk ⊢
    exact hR i hi hj k hk
  obtain ⟨q,hq,hqlen,hmem,hmarks,hedges,hdir⟩:=
    marked_wheel_directed_interval_with_edges (SimpleGraph.completeGraph V) v c n start C p' hp' hl' hs' hdis hend R hr'
  refine ⟨q,hq,hqlen,hmem,hmarks,?_,hdir⟩
  intro e
  rw [hedges e]
  constructor
  · rintro ⟨i,hi,hj,he⟩
    exact ⟨i,hi,hj,by simpa only [hmatch i hi hj] using he⟩
  · rintro ⟨i,hi,hj,he⟩
    exact ⟨i,hi,hj,by simpa only [hmatch i hi hj] using he⟩
end Oberwolfach
