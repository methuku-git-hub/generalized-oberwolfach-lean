module

public import Oberwolfach.MarkedSingleWheelDirectedWalk
public import Oberwolfach.MarkedSelectedWheelDirectedRun
public import Oberwolfach.MarkedWheelSpokeLabelsDisjoint
public import Oberwolfach.MarkedRunTerminalSeparation

@[expose] public section
/-! The selected marked wheels of one physical packing concatenate into the
actual directed target run, with every interval marker retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem packed_marked_wheels_form_directed_run
    {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    (G:SimpleGraph V) (tail head:E → V) (ktail khead:K → V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V → U → Prop)
    (v:ℕ → V) (start n:ℕ) (hne:∀ i,v i≠v (i+1)) (hnext:∀ i,v (i+1)=π (v i))
    (W:∀ i,start ≤ i → i < start+n → MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hroot:∀ i (hi:start ≤ i) (hj:i < start+n),(W i hi hj).1.val 0=v i)
    (hpair:∀ i j (hi:start ≤ i) (hj:i < start+n) (hi':start ≤ j) (hj':j < start+n),i≠j → 
      Disjoint (markedWheelPhysicalResources (W i hi hj)) (markedWheelPhysicalResources (W j hi' hj')))
    (hhub:∀ i j (hi:start ≤ i) (hj:i < start+n) (hi':start ≤ j) (hj':j < start+n),
      (W i hi hj).2.val=(W j hi' hj').2.val)
    (hterminal:∀ i (hi:start ≤ i) (hj:i < start+n),∀ a:Fin (m+1),
      v (start+n)≠(W i hi hj).1.val a)
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:K,G.Adj (ktail e) (π (khead e)))
    (R:V → V → Prop) (hER:∀e:E,R (tail e) (head e)) (hKR:∀e:K,R (ktail e) (π (khead e))):
    ∃q:(SimpleGraph.completeGraph V).Walk (v start) (v (start+n)),q.IsPath ∧ q.length=n*(m+1) ∧
      (∀x,x∈q.support ↔ x=v (start+n) ∨
        ∃ i, ∃ hi:start ≤ i, ∃ hj:i < start+n, ∃ a:Fin (m+1),(W i hi hj).1.val a=x) ∧
      (∀ j,j≤n → q.getVert ((m+1)*j)=v (start+j)) ∧
      (∀ k,k<q.length → R (q.getVert k) (q.getVert (k+1))):=by
  classical
  let C (i:ℕ):Fin (m+1) → V:=if h:start ≤ i ∧ i < start+n then (W i h.1 h.2).1.val else fun _=>v 0
  have hC:∀ i (hi:start ≤ i) (hj:i < start+n),C i=(W i hi hj).1.val:=by
    intro i hi hj
    dsimp only [C]
    split_ifs with h
    · rfl
    · exact False.elim (h ⟨hi,hj⟩)
  have he:∀e:E,(SimpleGraph.completeGraph V).Adj (tail e) (head e):=by
    intro e
    simpa only [SimpleGraph.completeGraph_eq_top,SimpleGraph.top_adj] using (hE e).ne
  have hk:∀e:K,(SimpleGraph.completeGraph V).Adj (ktail e) (π (khead e)):=by
    intro e
    simpa only [SimpleGraph.completeGraph_eq_top,SimpleGraph.top_adj] using (hK e).ne
  have hex:∀ i (hi:start ≤ i) (hj:i < start+n),∃p:(SimpleGraph.completeGraph V).Walk (v i) (v (i+1)),
      p.IsPath ∧ p.length=m+1 ∧ p.support.dropLast=List.ofFn (C i) ∧
      ∀ k,k<p.length → R (p.getVert k) (p.getVert (k+1)):=by
    intro i hi hj
    have hr:π ((W i hi hj).1.val 0)≠(W i hi hj).1.val 0:=by
      rw [hroot i hi hj,←hnext i]
      exact (hne i).symm
    obtain ⟨p,hp,hl,hs,hR⟩:=marked_single_wheel_directed_walk (SimpleGraph.completeGraph V) tail head ktail khead m b π hb (W i hi hj).1 hr he hk R hER hKR
    let p':(SimpleGraph.completeGraph V).Walk (v i) (v (i+1)):=p.copy (hroot i hi hj) (by rw [hroot i hi hj];exact (hnext i).symm)
    refine ⟨p',?_,?_,?_,?_⟩
    · simpa only [p',SimpleGraph.Walk.isPath_copy] using hp
    · simpa only [p',SimpleGraph.Walk.length_copy] using hl
    · simpa only [p',SimpleGraph.Walk.support_copy,hC i hi hj] using hs
    · simpa only [p',SimpleGraph.Walk.length_copy,SimpleGraph.Walk.getVert_copy] using hR
  choose p hp hlen hsupport hR using hex
  have hdis:∀ i j,start ≤ i → i < start+n → start ≤ j → j < start+n → i≠j → ∀a b':Fin (m+1),C i a≠C j b':=by
    intro i j hi hj hi' hj' hij a b'
    rw [hC i hi hj,hC j hi' hj']
    exact disjoint_marked_wheels_distinct_spoke_labels (W i hi hj) (W j hi' hj') (hpair i j hi hj hi' hj' hij) (hhub i j hi hj hi' hj') a b'
  have hend:∀ i,start ≤ i → i < start+n → ∀ a:Fin (m+1),v (start+n)≠C i a:=by
    intro i hi hj a
    rw [hC i hi hj]
    exact hterminal i hi hj a
  obtain ⟨q,hq,hqlen,hmem,hmarks,hqR⟩:=selected_marked_wheel_directed_run v (m+1) n start hne C p hp hlen hsupport hdis hend R hR
  refine ⟨q,hq,hqlen,?_,hmarks,hqR⟩
  intro x
  rw [hmem x]
  constructor
  · rintro (h|⟨i,hi,hj,a,ha⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,hi,hj,a,by simpa only [hC i hi hj] using ha⟩
  · rintro (h|⟨i,hi,hj,a,ha⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i,hi,hj,a,by simpa only [hC i hi hj] using ha⟩
end Oberwolfach
