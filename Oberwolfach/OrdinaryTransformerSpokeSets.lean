module

public import Oberwolfach.OrdinaryOneRootPathWheels
public import Oberwolfach.TransformerEndpointAssignments

@[expose] public section

/-! The sets used by the hub-switch factors are the actual disjoint
spoke-path vertex sets. Their cardinalities, divisibility and common-hub
adjacencies are derived from the original spoke incidence relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem spoke_index_fiber_card (H:V→U→Prop) (u:U):
    ((Finset.univ:Finset {e:V×U // H e.1 e.2}).filter (fun e=>e.val.2=u)).card=
      ((Finset.univ:Finset V).filter (fun v=>H v u)).card:=by
  apply Finset.card_bij (fun e _=>e.val.1)
  · intro e he
    have he':e.val.2=u:=(Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he' ▸ e.property⟩
  · intro e he f hf hval
    apply Subtype.ext
    exact Prod.ext hval ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  · intro v hv
    refine ⟨⟨(v,u),(Finset.mem_filter.mp hv).2⟩,by simp,rfl⟩

 theorem ordinary_transformer_spoke_sets (Q F:SimpleGraph V) (H K:V→U→Prop)
    (φ:U→U) (r:ℕ) (hr:3≤r)
    (p:{e:V×U // H e.1 e.2}→(Σ a:V,Σ b:V,Q.Walk a b))
    (hpath:∀ i,(p i).2.2.IsPath∧(p i).2.2.length=r-2)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hF:∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w)
    (hH:∀ i,∀ v∈(p i).2.2.support,K v i.val.2∧K v (φ i.val.2))
    (hdiv:∀ u,r∣((Finset.univ:Finset V).filter (fun v=>H v u)).card):
    let Z:U→Finset V:=fun u=>(Finset.univ.filter (fun i:{e:V×U // H e.1 e.2}=>i.val.2=u)).biUnion
      (fun i=>(p i).2.2.support.toFinset)
    (∀ u,(Z u).card=(r-1)*((Finset.univ:Finset V).filter (fun v=>H v u)).card) ∧
    (∀ u,r∣(Z u).card) ∧ (∀ u u',u≠u'→Disjoint (Z u) (Z u')) ∧
    (∀ u,∀ v∈Z u,K v u∧K v (φ u)) ∧
    (∀ u,∀ v∈Z u,∀ w∈Z u,¬F.Adj v w):=by
  dsimp only
  let J:={e:V×U // H e.1 e.2}
  let I:U→Finset J:=fun u=>Finset.univ.filter (fun i=>i.val.2=u)
  let Z:U→Finset V:=fun u=>(I u).biUnion (fun i=>(p i).2.2.support.toFinset)
  have hsize (i:J):(p i).2.2.support.toFinset.card=r-1:=by
    rw [List.toFinset_card_of_nodup (hpath i).1.support_nodup,(p i).2.2.length_support,(hpath i).2]
    omega
  have hZcard (u:U):(Z u).card=(r-1)*((Finset.univ:Finset V).filter (fun v=>H v u)).card:=by
    change ((I u).biUnion (fun i=>(p i).2.2.support.toFinset)).card=_
    rw [Finset.card_biUnion (by intro i _ j _ hij;exact hdis i j hij)]
    simp only [hsize,Finset.sum_const,nsmul_eq_mul]
    rw [show (I u).card=((Finset.univ:Finset V).filter (fun v=>H v u)).card from spoke_index_fiber_card H u,Nat.mul_comm]
    norm_cast
  refine ⟨hZcard,?_,?_,?_,?_⟩
  · intro u
    rw [hZcard]
    exact dvd_mul_of_dvd_right (hdiv u) (r-1)
  · intro u u' huu'
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨i,hi,hvi⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨j,hj,hvj⟩:=Finset.mem_biUnion.mp hv'
    have hij:i≠j:=by
      intro he
      have hi':i.val.2=u:=(Finset.mem_filter.mp hi).2
      have hj':j.val.2=u':=(Finset.mem_filter.mp hj).2
      exact huu' (hi'.symm.trans ((congrArg (fun e:J=>e.val.2) he).trans hj'))
    exact Finset.disjoint_left.mp (hdis i j hij) hvi hvj
  · intro u v hv
    obtain ⟨i,hi,hv⟩:=Finset.mem_biUnion.mp hv
    have hi':i.val.2=u:=(Finset.mem_filter.mp hi).2
    simpa only [hi'] using hH i v (List.mem_toFinset.mp hv)
  · intro u v hv w hw
    obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨j,_,hw⟩:=Finset.mem_biUnion.mp hw
    exact hF i j v (List.mem_toFinset.mp hv) w (List.mem_toFinset.mp hw)

 theorem balanced_spoke_root_separation (G F:SimpleGraph V) (H:V→U→Prop) (φ:V→V)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H v)).card)
    (hsep:∀ v w,G.Adj v w→¬F.Adj v (φ v)):
    ∀ v u,H v u→¬F.Adj v (φ v):=by
  intro v u hvu
  have hpos:0<((Finset.univ:Finset U).filter (H v)).card:=
    Finset.card_pos.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvu⟩⟩
  have hdeg:0<G.degree v:=by rw [hbalance];omega
  have hn:(G.neighborFinset v).Nonempty:=Finset.card_pos.mp (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg)
  obtain ⟨w,hw⟩:=hn
  exact hsep v w ((G.mem_neighborFinset v w).mp hw)

end Oberwolfach
