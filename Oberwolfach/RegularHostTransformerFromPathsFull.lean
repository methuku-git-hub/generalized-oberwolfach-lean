module

public import Oberwolfach.RegularHostTransformerFromPathsSucc
public import Oberwolfach.OrdinaryTransformerFromProfiles
public import Oberwolfach.UniformNamedSubgraphTransformer

@[expose] public section
/-! Construct the ordinary transformer from the prescribed path and wheel
stage in a regular host, using root-separated hub trades above the ordinary
cycle-decomposition threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_transformer_from_paths_regular_host (r:ℕ) (hr:3≤r)
    (α:ℝ) (hα:0<α) (hα1:α≤1):
    ∃ ξ:ℝ,0<ξ ∧ ∀ q nU:ℕ,∃ t:ℕ,∀ (F₀ d:ℝ) (f:ℕ),0≤F₀→0≤d→∃ N₀:ℕ,
    ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],N₀≤Fintype.card V→
      ∀ (G Q GHost F Fdel:SimpleGraph V) (Dhost:ℕ),
      GHost.IsRegularOfDegree Dhost→Fdel.edgeFinset.card≤f→
      cycleThreshold r+α≤(Dhost:ℝ)/Fintype.card V→
      Q=GHost\Fdel→
      ∀ (H₀ H:V→U→Prop),
      (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ξ*Fintype.card V)→
      ∀ (φ:V→V) (ψ:U→U)
      (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
      (σ:∀ v,Equiv.Perm (G.neighborSet v)),(∀ v w,σ v w≠w)→
      ∀ p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c),
      ∀ (A R W:Finset V) (B:Finset U),R⊆W→
      (∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)→
      (∀ u,r∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)→
      (∀ u,((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤q)→
      Fintype.card {u:U // ∃ v,H₀ v u}≤nU→
      (∀ v∈G.support,v∈R∧φ v∈R)→
      (∀ v∈G.support,∀ w∈G.support,φ v≠w)→
      (∀ u,(∃ v,H₀ v u)→u≠ψ u)→
      (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
      Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2))→
      Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2))→
      (∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)→
      (∀ i,(p i).2.2.IsPath)→(r≠3→∀ i,0<(p i).2.2.length)→
      (r=3→∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)→
      (r=3→∀ d:Σ v,G.neighborSet v,Q.Adj (transformerRimEndpoint G Q H₀ p d)
        (transformerSpokeEndpoint G Q H₀ b p d))→
      (∀ i:{e:V×U // H₀ e.1 e.2},(p (.inr i)).2.2.length=r-2)→
      (∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)→
      (∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)→
      (∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w)→
      (∀ i,∀ v∈(p i).2.2.support,∀ w∈R,¬F.Adj v w)→
      (∀ e:G.edgeFinset,Q.Adj e.val.out.1 (p (.inl e)).1 ∧
        Q.Adj (φ e.val.out.1) (p (.inl e)).1 ∧ Q.Adj e.val.out.2 (p (.inl e)).2.1 ∧
        Q.Adj (φ e.val.out.2) (p (.inl e)).2.1)→
      (∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (p (.inr e)).1 ∧
        Q.Adj (φ e.val.1) (p (.inr e)).1 ∧ Q.Adj e.val.1 (p (.inr e)).2.1 ∧
        Q.Adj (φ e.val.1) (p (.inr e)).2.1)→
      (∀ v,(F.degree v:ℝ)≤d)→∀ c:ℝ,
      (r≠3→∀ u v w,c≤(((A.filter (fun x=>H x u))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r≠3→W.card+Fintype.card (Σ v,G.neighborSet v)*r+((r:ℝ)+4)*(d+1)<c)→
      W.card+2*(r:ℝ)*Fintype.card (Σ v,G.neighborSet v)≤F₀→
      ∀ E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p,
      ∀ S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p,
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        N.card≤r*(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2}+Fintype.card (Σ v,G.neighborSet v))+nU*(t+r*q)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈N∧v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈N)∧
        (∀ v∈R,∀ v'∈R,Sum.inl s(v,v')∉K)∧
        (∀ v∈R,∀ a∈B,Sum.inr (v,a)∉K):=by
  cases r with
  | zero => omega
  | succ m =>
    have hm:2≤m:=by omega
    have hh:=ordinary_transformer_from_paths_regular_host_succ m hm α hα hα1
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_succ,Nat.succ_eq_add_one] using hh
end Oberwolfach
