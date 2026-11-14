module

public import Oberwolfach.MarkedFreshFactorOnHubDomain
public import Oberwolfach.FixedDomainQuadraticEvent
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! One physical sampling event supplies marked factors at every specified
hub, for every later allowed choice of the factor classes and forbidden
physical rim graph. No independence between the hub events is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def hubSpokeCoin {A U:Type} (u:U):A↪Sym2 (A⊕U) where
  toFun v:=s(Sum.inl v,Sum.inr u)
  inj':=by
    intro v w h
    rcases Sym2.eq_iff.mp h with ⟨h,_⟩|⟨h,_⟩
    · exact Sum.inl.inj h
    · exact (Sum.inl_ne_inr h).elim

theorem marked_fresh_hub_common_event (m:ℕ) (hm:3<m+1) (β κ bLo B:ℝ)
    (hβ:0<β) (hκ:0<κ) (hbLo:0<bLo) (hB:0≤B) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
    ∀ (A U E K J:Type) [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U] [Fintype J],
      N≤Fintype.card A→Fintype.card J≤(Fintype.card A)^2→
    ∀ (tail head:E→A) (ktail khead:K→A) (π:Equiv.Perm A) (b:ℕ)
      (H₀ HK:A→U→Prop) (u:J→U),
      (∀ j v,¬(H₀ v (u j)∧HK v (u j)))→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→
      (∀ j v z,H₀ v (u j)→HK z (u j)→v≠π z)→
      (∀ j,κ*Fintype.card A≤((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).card:ℝ))→
      (∀ j,β*(Fintype.card A:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ HK (u j)))→
      (∀ j i,∀ v v':A,v≠v'→(if i then HK v (u j) else H₀ v (u j))→(if i then HK v' (u j) else H₀ v' (u j))→
        β*(Fintype.card A:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ HK i v v' (u j) (u j)))→
      ∀ wt:∀ j,HubMarkedCycle tail head ktail khead m π b H₀ HK (u j)→ℝ,
      (∀ j C,bLo/(Fintype.card A:ℝ)^m≤wt j C ∧ wt j C≤B/(Fintype.card A:ℝ)^m)→
      (∀ j v,H₀ v (u j)∨HK v (u j)→|1-hypergraphWeightedDegree (hubMarkedCycleVertices (u j)) (wt j) v|≤η)→
      1-1/(Fintype.card A:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (A⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ j (Y:Finset A),(∀ v∈Y,H₀ v (u j)∨HK v (u j))→
          (Y.filter (fun v=>H₀ v (u j))).card=m*(Y.filter (fun v=>HK v (u j))).card→
          ((changed Y ((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).filter
            (fun v=>σ s(Sum.inl v,Sum.inr (u j))=true))).card:ℝ)≤ζ*(p*Fintype.card A)→
          ∀ F:SimpleGraph A,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card A))→
          ∃ D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK (u j)),
            ((∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubMarkedCycleVertices (u j) C) (hubMarkedCycleVertices (u j) C')) ∧
              D.biUnion (hubMarkedCycleVertices (u j))=Y) ∧
            Disjoint (physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges (u j)))) F ∧
            (∀ v,(physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges (u j)))).degree v≤2) ∧
            (∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubCyclePhysicalEdges (u j) C) (hubCyclePhysicalEdges (u j) C'))) := by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_fresh_factor_on_hub_domain m hm β κ bLo B hβ hκ hbLo hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 (q+3)
  obtain ⟨Nc,hNc⟩:=fixed_domain_quadratic_common_event κ hκ q
  refine ⟨max Nf Nc,?_⟩
  intro A U E K J _ _ _ _ _ hn hJ tail head ktail khead π b H₀ HK u hd hphys hsep hsize hbase hpath wt hw herr
  let μ:=FiniteLaw.pi (fun _:Sym2 (A⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)
  let P:J→(Sym2 (A⊕U)→Bool)→Prop:=fun j σ=>∀ Y:Finset A,(∀ v∈Y,H₀ v (u j)∨HK v (u j))→
    (Y.filter (fun v=>H₀ v (u j))).card=m*(Y.filter (fun v=>HK v (u j))).card→
    ((changed Y ((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).filter
      (fun v=>σ s(Sum.inl v,Sum.inr (u j))=true))).card:ℝ)≤ζ*(p*Fintype.card A)→
    ∀ F:SimpleGraph A,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card A))→
    ∃ D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK (u j)),
      ((∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubMarkedCycleVertices (u j) C) (hubMarkedCycleVertices (u j) C')) ∧
        D.biUnion (hubMarkedCycleVertices (u j))=Y) ∧
      Disjoint (physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges (u j)))) F ∧
      (∀ v,(physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges (u j)))).degree v≤2) ∧
      (∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubCyclePhysicalEdges (u j) C) (hubCyclePhysicalEdges (u j) C'))
  have hP (j:J):1-1/((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).card:ℝ)^(q+3)≤μ.probability (P j):=by
    have hh:=hNf A U E K (by omega) tail head ktail khead π b H₀ HK (u j)
      (hd j) hphys (hsep j) (hsize j) (hbase j) (hpath j) (wt j) (hw j) (herr j)
    rw [←finiteLaw_pi_injective_projection_event
      (fun _:Sym2 (A⊕U)=>FiniteLaw.retentionCoin p hp.le hp1) (hubSpokeCoin (u j)) (hubSpokeCoin (u j)).injective] at hh
    exact hh
  exact hNc (Fintype.card A) (by omega) (Sym2 (A⊕U)→Bool) J hJ μ
    (fun j=>(Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).card) P hsize hP

end Oberwolfach
