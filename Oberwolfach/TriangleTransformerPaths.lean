module

public import Oberwolfach.TriangleTransformerVertices
public import Oberwolfach.TransformerActualData

@[expose] public section

/-! Convert the selected triangular vertices into actual graph paths:
a zero-length path at each p_e and the single edge a_f b_f at each spoke.
The incidence bijection supplies the required p_e--z adjacency exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 13000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem triangular_transformer_paths (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (A W R:Finset V) (d c:ℝ) (hd:0≤d) (hF:∀ w,(F.degree w:ℝ)≤d)
    (hfour:∀ w x y z,c≤((A.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))
    (hspfour:∀ u u' w x y z,c≤((A.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+G.edgeFinset.card+2*Fintype.card {e:V×U // H₀ e.1 e.2}+1)*(d+1)<c):
    ∃ p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c),
      (∀ i,(p i).2.2.IsPath)∧
      (∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)∧
      (∀ e:{e:V×U // H₀ e.1 e.2},(p (.inr e)).2.2.length=1)∧
      (∀ i,∀ v∈(p i).2.2.support,v∈A∧v∉W∧v∉R∧∀ w∈R,¬F.Adj v w)∧
      (∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)∧
      (∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w)∧
      (∀ e:G.edgeFinset,Q.Adj e.val.out.1 (p (.inl e)).1∧Q.Adj (φ e.val.out.1) (p (.inl e)).1∧
        Q.Adj e.val.out.2 (p (.inl e)).2.1∧Q.Adj (φ e.val.out.2) (p (.inl e)).2.1)∧
      (∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (p (.inr e)).1∧Q.Adj (φ e.val.1) (p (.inr e)).1∧
        Q.Adj e.val.1 (p (.inr e)).2.1∧Q.Adj (φ e.val.1) (p (.inr e)).2.1)∧
      (∀ e:{e:V×U // H₀ e.1 e.2},∀ v∈(p (.inr e)).2.2.support,H v e.val.2∧H v (ψ e.val.2))∧
      ∀ d:Σ v,G.neighborSet v,Q.Adj (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d):=by
  let J:={e:V×U // H₀ e.1 e.2}
  let e₀:J→G.edgeFinset:=fun i=>(rimIncidenceEquiv G ((spokeEndpointEquiv G H₀ b).symm (i,0))).1
  let e₁:J→G.edgeFinset:=fun i=>(rimIncidenceEquiv G ((spokeEndpointEquiv G H₀ b).symm (i,1))).1
  obtain ⟨p₀,a,z,hp,hends,haz,havoid,hdis,hpp,hzz⟩:=triangular_transformer_vertices Q F H A W R
    (fun e:G.edgeFinset=>e.val.out.1) (fun e=>e.val.out.2) (fun e=>φ e.val.out.1) (fun e=>φ e.val.out.2)
    (fun i:J=>i.val.1) (fun i=>φ i.val.1) (fun i=>i.val.2) (fun i=>ψ i.val.2) e₀ e₁ d c hd hF hfour
    (fun i=>hspfour i.val.2 (ψ i.val.2)) (by simpa only [Fintype.card_coe] using hbudget)
  have hazQ (i:J):Q.Adj (a i) (z i):=(haz i).2.2.2.2.2.2.2.2.1
  let p:(G.edgeFinset⊕J)→(Σ a:V,Σ c:V,Q.Walk a c):=Sum.elim
    (fun e=>⟨p₀ e,p₀ e,SimpleGraph.Walk.nil⟩)
    (fun i=>⟨a i,z i,(SimpleGraph.Walk.nil).cons (hazQ i)⟩)
  have hs₀ (e:G.edgeFinset) (v:V):v∈(p (.inl e)).2.2.support↔v=p₀ e:=by simp [p]
  have hs₁ (i:J) (v:V):v∈(p (.inr i)).2.2.support↔v∈({a i,z i}:Finset V):=by simp [p]
  have hs₀' (e:G.edgeFinset):(p (.inl e)).2.2.support.toFinset={p₀ e}:=by ext v;simp [p]
  have hs₁' (i:J):(p (.inr i)).2.2.support.toFinset={a i,z i}:=by ext v;simp [p]
  refine ⟨p,?_,by intro e;rfl,by intro e;rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    cases i with
    | inl e=>simp [p]
    | inr i=>
      change ((SimpleGraph.Walk.nil).cons (hazQ i)).IsPath
      apply SimpleGraph.Walk.IsPath.cons
      · exact SimpleGraph.Walk.IsPath.nil
      · simpa using (hazQ i).ne
  · intro i v hv
    cases i with
    | inl e=>rw [(hs₀ e v).mp hv];exact hp e
    | inr i=>
      have hv':=(hs₁ i v).mp hv
      have ha:=havoid i v hv'
      refine ⟨?_,ha.1,ha.2.1,ha.2.2.2.1⟩
      rcases Finset.mem_insert.mp hv' with he|he
      · exact he.symm ▸ (haz i).1
      · exact (Finset.mem_singleton.mp he).symm ▸ (haz i).2.1
  · intro i j hij
    cases i with
    | inl e=>
      cases j with
      | inl f=>rw [hs₀',hs₀'];simpa using (fun he=>hij (congrArg Sum.inl (p₀.injective he)))
      | inr f=>
        rw [hs₀',hs₁']
        apply Finset.disjoint_left.mpr
        intro v hv hw
        exact (havoid f v hw).2.2.1 e (Finset.mem_singleton.mp hv)
    | inr i=>
      cases j with
      | inl e=>
        rw [hs₁',hs₀']
        apply Finset.disjoint_left.mpr
        intro v hv hw
        exact (havoid i v hv).2.2.1 e (Finset.mem_singleton.mp hw)
      | inr j=>rw [hs₁',hs₁'];exact hdis i j (fun he=>hij (congrArg Sum.inr he))
  · intro i j v hv w hw
    cases i with
    | inl e=>
      rw [(hs₀ e v).mp hv]
      cases j with
      | inl f=>rw [(hs₀ f w).mp hw];exact hpp e f
      | inr f=>exact fun he=>(havoid f w ((hs₁ f w).mp hw)).2.2.2.2 e he.symm
    | inr i=>
      cases j with
      | inl e=>rw [(hs₀ e w).mp hw];exact (havoid i v ((hs₁ i v).mp hv)).2.2.2.2 e
      | inr j=>exact hzz i j v ((hs₁ i v).mp hv) w ((hs₁ j w).mp hw)
  · intro e;exact ⟨(hends e).1,(hends e).2.2.1,(hends e).2.1,(hends e).2.2.2⟩
  · intro i;exact ⟨(haz i).2.2.1,(haz i).2.2.2.1,(haz i).2.2.2.2.2.1,(haz i).2.2.2.2.2.2.1⟩
  · intro i v hv
    have hh:=(haz i).2.2.2.2.2.2.2.2.2
    rcases Finset.mem_insert.mp ((hs₁ i v).mp hv) with rfl|hv
    · exact ⟨hh.1,hh.2.1⟩
    · rw [Finset.mem_singleton.mp hv];exact ⟨hh.2.2.1,hh.2.2.2⟩
  · intro d₀
    have hd₀:(spokeEndpointEquiv G H₀ b).symm (spokeEndpointEquiv G H₀ b d₀)=d₀:=
      (spokeEndpointEquiv G H₀ b).symm_apply_apply d₀
    let i: J:=(spokeEndpointEquiv G H₀ b d₀).1
    have ha (d₁:Σ v,G.neighborSet v):transformerRimEndpoint G Q H₀ p d₁=p₀ (rimIncidenceEquiv G d₁).1:=by
      simp [transformerRimEndpoint,graphPathEndpoint,p]
    rw [ha]
    change Q.Adj (p₀ (rimIncidenceEquiv G d₀).1)
      (if (spokeEndpointEquiv G H₀ b d₀).2=0 then a i else z i)
    split_ifs with he
    · have hid:(rimIncidenceEquiv G d₀).1=e₀ i:=by
        dsimp [e₀,i]
        rw [←he,hd₀]
      rw [hid];exact (haz i).2.2.2.2.1
    · have he1:(spokeEndpointEquiv G H₀ b d₀).2=1:=by omega
      have hid:(rimIncidenceEquiv G d₀).1=e₁ i:=by
        dsimp [e₁,i]
        rw [←he1,hd₀]
      rw [hid];exact (haz i).2.2.2.2.2.2.2.1

end Oberwolfach
