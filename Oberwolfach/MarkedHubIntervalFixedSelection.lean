module

public import Oberwolfach.MarkedFiniteWheelIntervalPathEdges
public import Oberwolfach.MarkedHubFactorRootSelection

@[expose] public section
/-! Reconstruct a single successor interval as a simple path from an actual
vertex-disjoint marked hub factor, preserving the factor vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_interval_path_for_selection
    {V U E K:Type*} [Fintype V] [instV:DecidableEq V] {n:ℕ}
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V→U→Prop) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀C∈M,∀D∈M,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D))
    (S Y:Finset V) (hcover:M.biUnion (hubMarkedCycleVertices u)=S)
    (hYS:Y⊆S) (hmarked:∀x∈Y,Hₖ x u) (hsep:∀x,Hₖ x u→¬H₀ x u)
    (select:{x // x∈Y}↪HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u)
    (hselected:∀x,select x∈M ∧ (select x).val 0=x.val)
    (v:Fin (n+1)↪V) (hroots:∀i:Fin n,v i.castSucc∈Y)
    (hnext:∀i:Fin n,π (v i.castSucc)=v i.succ) (hend:v (Fin.last n)∉S)
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:K,G.Adj (ktail e) (π (khead e))):
    ∃q:G.Walk (v 0) (v (Fin.last n)),q.IsPath ∧ q.length=n*(m+1) ∧
      (∀x,x∈q.support ↔ x=v (Fin.last n) ∨
        ∃i:Fin n,∃a:Fin (m+1),(select ⟨v i.castSucc,hroots i⟩).val a=x) ∧
      walkPhysicalEdges q=Finset.univ.biUnion (fun i:Fin n=>
        markedCyclePhysicalEdges tail head ktail khead m π b
          ⟨(select ⟨v i.castSucc,hroots i⟩).val,(select ⟨v i.castSucc,hroots i⟩).property.1⟩) := by
  let C:Fin n→MarkedCycleTuple tail head ktail khead m π b:=fun i=>
    ⟨(select ⟨v i.castSucc,hroots i⟩).val,(select ⟨v i.castSucc,hroots i⟩).property.1⟩
  have hS:∀D∈M,hubMarkedCycleVertices u D⊆S:=by
    intro D hD x hx
    rw [←hcover]
    exact Finset.mem_biUnion.mpr ⟨D,hD,hx⟩
  obtain ⟨hpair,hterminal⟩:=marked_hub_factor_interval_separation tail head ktail khead m b π H₀ Hₖ u M hM select
    (fun x=>(hselected x).1) S hS (v (Fin.last n)) hend
  have hroot:∀i,(C i).val 0=v i.castSucc:=fun i=>(hselected ⟨v i.castSucc,hroots i⟩).2
  have hsucc:∀i,π ((C i).val 0)=v i.succ:=by intro i;rw [hroot i];exact hnext i
  have hnofixed:∀i,π ((C i).val 0)≠(C i).val 0:=by
    intro i heq
    rw [hroot i,hnext i] at heq
    have hh:=congrArg Fin.val (v.injective heq)
    simp only [Fin.val_succ,Fin.val_castSucc] at hh
    omega
  have hdis:∀i j:Fin n,i≠j→∀a b:Fin (m+1),(C i).val a≠(C j).val b:=by
    intro i j hij a b
    have hne:(⟨v i.castSucc,hroots i⟩:{x // x∈Y})≠⟨v j.castSucc,hroots j⟩:=by
      intro heq
      have hv:=congrArg Subtype.val heq
      exact hij (Fin.castSucc_injective n (v.injective hv))
    exact hpair ⟨v i.castSucc,hroots i⟩ ⟨v j.castSucc,hroots j⟩ hne a b
  have hend':∀i:Fin n,∀a:Fin (m+1),v (Fin.last n)≠(C i).val a:=by
    intro i a
    exact hterminal ⟨v i.castSucc,hroots i⟩ a
  obtain ⟨q,hq,hlen,hsupport,hedges⟩:=marked_finite_wheel_interval_path_with_edges G tail head ktail khead m b π hb v C hroot hsucc hnofixed hE hK hdis hend'
  refine ⟨q,hq,hlen,hsupport,?_⟩
  have hdec:(instV:DecidableEq V)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  rw [hdec]
  exact hedges
end Oberwolfach
