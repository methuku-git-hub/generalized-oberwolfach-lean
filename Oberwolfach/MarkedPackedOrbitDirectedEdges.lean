module

public import Oberwolfach.MarkedPackedWheelDirectedEdges
public import Oberwolfach.MarkedOrbitTerminalSeparation

@[expose] public section
/-! The matching event's injective permutation interval and ordinary-spoke
exclusion discharge terminal separation for a packed marked-wheel run. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem packed_marked_wheels_form_orbit_run_with_edges
    {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    (G:SimpleGraph V) (tail head:E → V) (ktail khead:K → V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V → U → Prop)
    (a:V) (d start n:ℕ) (hbound:start+n≤d) (hπ:∀x,π x≠x)
    (hinj:Function.Injective (fun k:Fin (d+1)=>(π^k.val) a))
    (W:∀ i, start ≤ i  →  i < start+n  →  MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hroot:∀ i (hi:start ≤ i) (hj:i < start+n),(W i hi hj).1.val 0=(π^i) a)
    (hpair:∀ i j (hi:start ≤ i) (hj:i < start+n) (hi':start ≤ j) (hj':j < start+n),i≠j → 
      Disjoint (markedWheelPhysicalResources (W i hi hj)) (markedWheelPhysicalResources (W j hi' hj')))
    (hhub:∀ i j (hi:start ≤ i) (hj:i < start+n) (hi':start ≤ j) (hj':j < start+n),
      (W i hi hj).2.val=(W j hi' hj').2.val)
    (Ord:Finset V)
    (hOrd:∀ i (hi:start ≤ i) (hj:i < start+n) (z:Fin (m+1)),z.val≠0 → (W i hi hj).1.val z∈Ord)
    (havoid:(π^(start+n)) a∉Ord)
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:K,G.Adj (ktail e) (π (khead e)))
    (R:V → V → Prop) (hER:∀e:E,R (tail e) (head e)) (hKR:∀e:K,R (ktail e) (π (khead e))):
    ∃q:(SimpleGraph.completeGraph V).Walk ((π^start) a) ((π^(start+n)) a),q.IsPath ∧ q.length=n*(m+1) ∧
      (∀x,x∈q.support ↔ x=(π^(start+n)) a ∨
        ∃ i, ∃ hi:start ≤ i, ∃ hj:i < start+n, ∃ z:Fin (m+1),(W i hi hj).1.val z=x) ∧
      (∀ j,j≤n → q.getVert ((m+1)*j)=(π^(start+j)) a) ∧
      (∀e:Sym2 V,e∈q.edges → ∃ i, ∃ hi:start ≤ i, ∃ hj:i < start+n,
        e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W i hi hj).1) ∧
      (∀ k,k<q.length → R (q.getVert k) (q.getVert (k+1))):=by
  let v:ℕ → V:=fun i=>(π^i) a
  have hne:∀ i,v i≠v (i+1):=permutation_orbit_adjacent_ne π hπ a
  have hnext:∀ i,v (i+1)=π (v i):=by intro i; simp only [v,pow_succ',Equiv.Perm.mul_apply]
  have hterminal:∀ i (hi:start ≤ i) (hj:i < start+n) (z:Fin (m+1)),v (start+n)≠(W i hi hj).1.val z:=by
    intro i hi hj z heq
    by_cases hz:z.val=0
    · have hz':z=0:=Fin.ext (by simpa using hz)
      subst z
      have hh:=marked_orbit_subinterval_terminal_ne π a d start n hbound hinj i hi hj
      exact hh (heq.trans (hroot i hi hj))
    · apply havoid
      change v (start+n)∈Ord
      rw [heq]
      exact hOrd i hi hj z hz
  exact packed_marked_wheels_form_directed_run_with_edges G tail head ktail khead m b π hb H₀ Hₖ v start n hne hnext W hroot hpair hhub hterminal hE hK R hER hKR
end Oberwolfach
