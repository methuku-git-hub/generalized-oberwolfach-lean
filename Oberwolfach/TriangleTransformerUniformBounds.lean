module

public import Oberwolfach.TriangleUniformBudgetArithmetic

@[expose] public section
/-! Uniformize the explicit triangle-transformer budgets: the spoke error
is chosen before the bounded root complexity and the order thresholds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_active_hubs_le_spokes {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (H:V→U→Prop):Fintype.card {u:U // ∃v,H v u}≤Fintype.card {e:V×U // H e.1 e.2}:=by
  let f:{u:U // ∃v,H v u}→{e:V×U // H e.1 e.2}:=fun u=>
    ⟨(Classical.choose u.property,u.val),Classical.choose_spec u.property⟩
  apply Fintype.card_le_of_injective f
  intro u v h
  apply Subtype.ext
  exact congrArg (fun e:{e:V×U // H e.1 e.2}=>e.val.2) h

theorem triangle_hub_spoke_count_le {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (H:V→U→Prop) (u:U):
    ((Finset.univ:Finset V).filter (fun v=>H v u)).card≤Fintype.card {e:V×U // H e.1 e.2}:=by
  rw [←spoke_index_fiber_card H u]
  exact Finset.card_le_univ _

theorem triangle_transformer_uniform_bounded_inputs
    (β:ℝ) (hβ:0<β) (hβ1:β≤1):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q:ℕ,∃ s₀:ℕ,∀ s:ℕ,s₀≤s→3∣s→∃ N₀ M₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→M₀≤Fintype.card U→
    ∀ (G Q:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hdiv:∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hu:∀ u,(∃v,H₀ v u)→u≠ψ u)
    (hQ:G≤Q) (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun e:G.edgeFinset=>s(φ e.val.out.1,φ e.val.out.2)))
    (hψedge:Function.Injective (fun e:{e:V×U // H₀ e.1 e.2}=>(φ e.val.1,ψ e.val.2)))
    (hH:∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))
    (ε:ℝ) (hε:0≤ε) (hεsmall:ε≤ε₀)
    (hnearV:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (hnearU:∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))
    (hw:W.card≤q) (hr:R.card≤q) (hb:B.card≤q) (he:G.edgeFinset.card≤q)
    (ht:Fintype.card {e:V×U // H₀ e.1 e.2}≤q) (hd:Fintype.card (Σ v,G.neighborSet v)≤q),
    ∃ W' N:Finset V,∃ T:Finset (Sym2 V⊕(V×U)),∃ B':Finset U,
      W⊆W' ∧ W'.card≤W.card+2*(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})+
        6*Fintype.card (Σ v,G.neighborSet v) ∧
      Disjoint N W' ∧ N.card≤q*s ∧
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) T ∧
      T⊆ordinaryHostResources Q H ∧
      B'.card≤G.edgeFinset.card+2*Fintype.card {u:U // ∃v,H₀ v u} ∧
      (∀ v z,Sum.inr (v,z)∈T→z∈B') ∧
      (∀ v w,Sum.inl s(v,w)∈T→v∈W'∪N∧w∈W'∪N) ∧
      (∀ v z,Sum.inr (v,z)∈T→v∈W'∪N) ∧
      (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T) ∧
      (∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T) ∧
      (∀ v∈W,∀ w,Sum.inl s(v,w)∈T→v∈R) ∧
      (∀ v∈W,∀ z,Sum.inr (v,z)∈T→v∈R) ∧
      (∀ v z,z∈B→Sum.inr (v,z)∈T→∃ u,(∃x,H₀ x u) ∧ (z=u∨z=ψ u)) :=by
  refine ⟨β/64,by positivity,?_⟩
  intro q
  obtain ⟨s₀,hs⟩:=triangle_dense_transformer_from_explicit_budgets q (2*q) β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hsdiv
  obtain ⟨Nbase,hbase⟩:=hs s hs₀ hsdiv
  obtain ⟨M,hM⟩:=exists_nat_gt (64*(11*(q:ℝ)+1)/β)
  refine ⟨max Nbase M,4*q+1,?_⟩
  intro V U _ _ _ _ hn hm G Q H₀ H φ ψ R W B hRW hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hw hr hb he ht hd
  have hnbase:Nbase≤Fintype.card V:=(le_max_left _ _).trans hn
  have hMn:(M:ℝ)≤Fintype.card V:=Nat.cast_le.mpr ((le_max_right _ _).trans hn)
  have hnβ:64*(11*(q:ℝ)+1)≤β*(Fintype.card V:ℝ):=by
    have hh:64*(11*(q:ℝ)+1)<(M:ℝ)*β:=(div_lt_iff₀ hβ).mp hM
    nlinarith
  obtain ⟨hεβ,hEdge,hHub,hStage⟩:=triangle_budgets_from_uniform_root_bounds β ε q
    (Fintype.card V) (Fintype.card U) W.card R.card G.edgeFinset.card
    (Fintype.card {e:V×U // H₀ e.1 e.2}) (Fintype.card (Σ v,G.neighborSet v)) B.card
    hβ hβ1 hε hεsmall hnβ hm hw hr he ht hd hb
  have hsize:∀ u,2*((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤2*q:=by
    intro u
    exact Nat.mul_le_mul_left 2 ((triangle_hub_spoke_count_le H₀ u).trans ht)
  have hactive:Fintype.card {u:U // ∃v,H₀ v u}≤q:=(triangle_active_hubs_le_spokes H₀).trans ht
  exact hbase V U hnbase G Q H₀ H φ ψ R W B hRW hbalance hdiv hsize hactive hroot hcross hu hQ hφQ
    hφedge hψedge hH hB hdeg ε hε hεβ hnearV hnearU hEdge hHub hStage
end Oberwolfach
