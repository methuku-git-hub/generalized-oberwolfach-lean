module

public import Oberwolfach.OrdinaryTriangleInnerTerminalThreshold
public import Oberwolfach.OrdinaryTriangleRootFreeLocalSizes
public import Oberwolfach.OrdinaryVortexLocalSizeInputs
public import Oberwolfach.OrdinaryVortexBufferedDomains

@[expose] public section
/-! One threshold, selected after the conflict degree and before the host,
provides the root-free triangle certificate sizes at every vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_terminal_threshold
    (ε lamInner:ℝ) (hε:0<ε) (hlamInner:0<lamInner)
    (d n₀ Nreserve Nclean Ninner Nsafe Norder Nextra:ℕ):
    ∃M:ℕ,32≤M ∧ Nextra≤M ∧ 4/ε≤(M:ℝ) ∧ ((2*(3*d):ℕ):ℝ)≤lamInner*M ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β:ℝ) (Q:Vortex U P D β ε mv),
    (M:ℝ)≤ε*mv/2→∀i,i<Q.length→
    let I:=markedVortexInnerVertices Q i;
    let T:=ordinaryVortexBufferedVertices Q i 2;let W:=ordinaryVortexBufferedHubs Q i 2;
    M≤I.card ∧ ∀lamGeo:ℝ,lamGeo≤1/4→
      (T.card:ℝ)+W.card≤lamGeo*Fintype.card (markedVortexVertexType Q i)→
      n₀≤Fintype.card ↥(Finset.univ\T) ∧
      Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)) ∧
      Nclean≤Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) ∧
      Nsafe≤Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) ∧
      Norder≤Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) ∧
      Ninner≤I.card ∧ 32≤I.card ∧ 16≤Fintype.card (markedVortexVertexType Q i) ∧
      1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^1≤(1/16:ℝ) ∧
      (1/16:ℝ)+2/(Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ)≤1/8 :=by
  let Nbase:=max 64 (max Nextra (max (4*n₀) (max (4*Nreserve) (max Nclean (max Ninner (max Nsafe Norder))))))
  obtain ⟨M,hbase,h32,hfour,hconf⟩:=ordinary_triangle_inner_terminal_threshold ε lamInner hε hlamInner (2*(3*d)) Nbase
  refine ⟨M,h32,by dsimp [Nbase] at hbase;omega,hfour,hconf,?_⟩
  intro V U _ _ _ _ P D mv β Q hterminal i hi I T W
  have hM:M≤I.card:=by
    have hh:=Q.extended_card_at_least_threshold hterminal (by omega : i+1≤Q.length)
    have heq:=(marked_vortex_inner_cardinalities Q i).1
    exact heq.symm ▸ hh
  refine ⟨hM,?_⟩
  intro lamGeo hlamGeo hroot
  apply ordinary_triangle_root_free_local_sizes I T W n₀ Nreserve Nclean Ninner Nsafe Norder lamGeo hlamGeo hroot
  all_goals dsimp [Nbase] at hbase <;> omega
end Oberwolfach
