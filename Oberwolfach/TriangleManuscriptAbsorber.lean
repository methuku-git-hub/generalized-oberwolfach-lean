module

public import Oberwolfach.TriangleDenseHostAbsorberGraph

@[expose] public section
/-! The triangular-wheel absorber in the finite embedded-root formulation,
with one size threshold controlling both the hub part and the absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_manuscript_absorber (β:ℝ) (hβ:0<β):
  ∃ ε₀:ℝ,0<ε₀ ∧ ∀ m:ℕ,∃ M₀ N₀:ℕ,
  ∀ (V₀ U₀ V U:Type) [Fintype V₀] [Fintype U₀] [DecidableEq V₀] [DecidableEq U₀]
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→M₀≤Fintype.card U→Fintype.card V₀+Fintype.card U₀≤m→
  ∀ (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (Q:SimpleGraph V) (H:V→U→Prop)
    (φ:V₀↪V) (ψ:U₀↪U),
    (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀ u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
    (∀ v u,Hs v u→H (φ v) (ψ u))→
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))→
  ∀ ε:ℝ,0≤ε→ε≤ε₀→
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))→
    (∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))→
  ∃ (R:SimpleGraph V) (K:V→U→Prop),
    R≤Q ∧ (∀ v u,K v u→H v u) ∧ Disjoint R (G.map φ) ∧
    (∀ v u,¬(K v u∧ordinaryMappedSpokes Hs φ ψ v u)) ∧
    (ordinaryPhysicalGraph R K).support.toFinset.card≤M₀ ∧
    (∀ v∈Finset.univ.image φ,∀ w∈Finset.univ.image φ,¬R.Adj v w) ∧
    (∀ v∈Finset.univ.image φ,∀ u∈Finset.univ.image ψ,¬K v u) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) (ordinaryHostResources R K) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
      (ordinaryHostResources (R⊔G.map φ) (fun v u=>K v u∨ordinaryMappedSpokes Hs φ ψ v u)) :=by
  obtain ⟨ε₀,hε₀,hbase⟩:=triangle_dense_host_absorber_graph β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro m
  obtain ⟨N,K,habs⟩:=hbase m m
  let M:=max K (2*(5*ordinaryDiagramSize 3 m+2*m+4*K))
  refine ⟨M,N,?_⟩
  intro V₀ U₀ V U _ _ _ _ _ _ _ _ hn hU hm G Hs Q H φ ψ hbal hdiv hG hHs hdeg ε hε hεsmall hnearV hnearU
  have hUK:K≤Fintype.card U:=(le_max_left _ _).trans hU
  have hB:(Finset.univ.image ψ).card≤m:=by
    rw [Finset.card_image_of_injective _ ψ.injective,Finset.card_univ]
    omega
  obtain ⟨R,Ks,hQ,hH,hdis,hsp,hcard,hR,hK,hdec,hdec'⟩:=habs V₀ U₀ V U hn hUK hm G Hs Q H ∅ (Finset.univ.image ψ) φ ψ
    hbal hdiv hG hHs (by intro u;exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩)
    (by simp) hB hdeg ε hε hεsmall hnearV hnearU
  refine ⟨R,Ks,hQ,hH,hdis,hsp,?_,?_,?_,hdec,hdec'⟩
  · exact hcard.trans (by dsimp [M];simpa only [max_self] using (le_max_right K (2*(5*ordinaryDiagramSize 3 m+2*m+4*K))))
  · intro v hv w hw
    exact hR v (Finset.mem_union_left _ hv) w (Finset.mem_union_left _ hw)
  · intro v hv u hu
    exact hK v (Finset.mem_union_left _ hv) u hu
end Oberwolfach
