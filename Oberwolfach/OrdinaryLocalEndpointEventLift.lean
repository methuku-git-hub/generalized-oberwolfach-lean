module

public import Oberwolfach.OrdinaryInducedEndpointPairingLift
public import Oberwolfach.OrdinaryInducedFinsetChanges
public import Oberwolfach.OrdinaryNormalizedHubConflictDegree
public import Oberwolfach.FreshNeighbourPairPhysicalEvent

@[expose] public section
/-! A simultaneous endpoint event on a fixed induced physical domain
lifts to the original graph, retaining its local-scale error budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W K E:Type} [Fintype W] [Fintype K] [Fintype E]
  [DecidableEq W] [DecidableEq K] [DecidableEq E]

def OrdinaryLocalEndpointEvent (G F:SimpleGraph W) (T:Finset W) (S R:K→Finset W)
    (g:K→W↪E) (p ζ:ℝ) (σ:E→Bool):Prop:=
  ∀k (S' R':Finset W) (D:SimpleGraph W),S'⊆S k→R'⊆R k→
    ((changed S' ((S k).filter (fun v=>σ (g k v)=true))).card:ℝ)≤ζ*(p*T.card)→
    ((changed R' ((R k).filter (fun v=>σ (g k v)=true))).card:ℝ)≤ζ*(p*T.card)→
    (∀v,(D.degree v:ℝ)≤ζ*(p*T.card))→S'.card=2*R'.card→
    ∃P:EndpointPairing G F S' R',Disjoint P.graph D

theorem ordinary_local_endpoint_event_lift
    (G F:SimpleGraph W) (T:Finset W) (S R:K→Finset W) (g:K→W↪E)
    (p ζ:ℝ) (σ:E→Bool)
    (hST:∀k,S k⊆T) (hRT:∀k,R k⊆T) (hdis:∀k,Disjoint (S k) (R k))
    (hlocal:∀k (S' R':Finset {v:W // v∈T}) (D:SimpleGraph {v:W // v∈T}),
      S'⊆ordinaryInducedFinset T (S k)→R'⊆ordinaryInducedFinset T (R k)→
      ((changed S' ((ordinaryInducedFinset T (S k)).filter (fun v=>σ (g k v.val)=true))).card:ℝ)≤ζ*(p*T.card)→
      ((changed R' ((ordinaryInducedFinset T (R k)).filter (fun v=>σ (g k v.val)=true))).card:ℝ)≤ζ*(p*T.card)→
      (∀v,(D.degree v:ℝ)≤ζ*(p*T.card))→S'.card=2*R'.card→
      ∃P:EndpointPairing (G.induce (T:Set W)) (F.induce (T:Set W)) S' R',Disjoint P.graph D):
    OrdinaryLocalEndpointEvent G F T S R g p ζ σ:=by
  intro k S' R' D hS hR hchangeS hchangeR hD hratio
  have hS'T:S'⊆T:=hS.trans (hST k)
  have hR'T:R'⊆T:=hR.trans (hRT k)
  have hSi:ordinaryInducedFinset T S'⊆ordinaryInducedFinset T (S k):=by
    intro v hv
    simp only [ordinaryInducedFinset,Finset.mem_filter,Finset.mem_univ,true_and] at *
    exact hS hv
  have hRi:ordinaryInducedFinset T R'⊆ordinaryInducedFinset T (R k):=by
    intro v hv
    simp only [ordinaryInducedFinset,Finset.mem_filter,Finset.mem_univ,true_and] at *
    exact hR hv
  have hchangeS':((changed (ordinaryInducedFinset T S')
      ((ordinaryInducedFinset T (S k)).filter (fun v=>σ (g k v.val)=true))).card:ℝ)≤ζ*(p*T.card):=by
    have he:((ordinaryInducedFinset T (S k)).filter (fun v=>σ (g k v.val)=true))=
        ordinaryInducedFinset T ((S k).filter (fun v=>σ (g k v)=true)):=by
      ext v
      simp [ordinaryInducedFinset]
    rw [he]
    rw [ordinary_induced_finset_changed_card T S' ((S k).filter (fun v=>σ (g k v)=true))
      hS'T ((Finset.filter_subset _ _).trans (hST k))]
    exact hchangeS
  have hchangeR':((changed (ordinaryInducedFinset T R')
      ((ordinaryInducedFinset T (R k)).filter (fun v=>σ (g k v.val)=true))).card:ℝ)≤ζ*(p*T.card):=by
    have he:((ordinaryInducedFinset T (R k)).filter (fun v=>σ (g k v.val)=true))=
        ordinaryInducedFinset T ((R k).filter (fun v=>σ (g k v)=true)):=by
      ext v
      simp [ordinaryInducedFinset]
    rw [he]
    rw [ordinary_induced_finset_changed_card T R' ((R k).filter (fun v=>σ (g k v)=true))
      hR'T ((Finset.filter_subset _ _).trans (hRT k))]
    exact hchangeR
  have hD':∀v:{v:W // v∈T},((D.induce (T:Set W)).degree v:ℝ)≤ζ*(p*T.card):=by
    intro v
    have hh:((D.induce (T:Set W)).degree v:ℝ)≤D.degree v.val:=by
      exact_mod_cast ordinary_induced_degree_le D T v
    exact hh.trans (hD v.val)
  have hratio':(ordinaryInducedFinset T S').card=2*(ordinaryInducedFinset T R').card:=by
    rw [ordinary_induced_finset_card T S' hS'T,ordinary_induced_finset_card T R' hR'T]
    exact hratio
  obtain ⟨P,hP⟩:=hlocal k (ordinaryInducedFinset T S') (ordinaryInducedFinset T R')
    (D.induce (T:Set W)) hSi hRi hchangeS' hchangeR' hD' hratio'
  exact ordinary_induced_endpoint_pairing_avoiding_lift G F D T S' R' hS'T hR'T
    ((hdis k).mono hS hR) P hP
end Oberwolfach
