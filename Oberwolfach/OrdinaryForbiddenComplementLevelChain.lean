module

public import Oberwolfach.OrdinaryForbiddenCompletionInputs
public import Oberwolfach.OrdinaryReservoirSurvivesComplement
public import Oberwolfach.OrdinaryInnerSpokeTargets
public import Oberwolfach.OrdinaryBalancedLevelChainTwoHosts
public import Oberwolfach.OrdinaryComplementRemainderBalance

@[expose] public section
/-! Conditional assembly of the actual forced-target complement, the protected
    reference reservoir, the level chain and the factor decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_forbidden_complement_factors_from_two_host_level_chain {n q r m:ℕ}
    (Target Sample Reference Protect Fbad:SimpleGraph (Fin n))
    (hTarget:Target.IsRegularOfDegree (2*q)) (hr:0<r)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q)) (Href:Fin n→Fin q→Prop)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (hsizeC:∀u (c:↥(C u)),Fintype.card c.val=r)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old E:Fin q→Finset (Sym2 (Fin n))) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hRef:Reference≤Sample)
    (hProtect:Protect≤Reference)
    (hAref:A⊆ordinaryHostResources Reference Href)
    (hReserveProtect:ordinaryResourceRim Reference A≤Protect)
    (hReserveTarget:ordinaryResourceRim Reference A≤Target)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (f u x) (f u y))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪E u)
    (hcover:∀e∈(ordinaryForbiddenRequired Target Sample Reference Fbad Inner).edgeFinset,∃u,e∈E u)
    (hAvoid:∀u x,¬Href (f u x) u)
    (hSpokeCover:∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Href u→∃x,f u x=v)
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (f u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (f v)))
    (W:Finset (Fin n)) (B:Finset (Fin q)) (hm:W.card+B.card≤m) (hW:W⊆Inner) (hB:B⊆Hubs)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=Reference) (F:=Fbad) (Hbase:=Href) (r:=r)) A)
    (hres:∀(G':SimpleGraph (Fin n)) (H':Fin n→Fin q→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources W B →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤Reference → (∀v u,H' v u→Href v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=Reference) (F:=Fbad) (Hbase:=Href) (r:=r))
        (ordinaryHostResources G' H') A):
    let Q:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u);
    ∀ (L:ℕ) (Good:ℕ→Finset (Sym2 (Fin n)⊕(Fin n×Fin q))→Prop),
    Good 0 (ordinaryHostResources Q H\A) →
    (∀i<L,∀S (G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop),
      Good i S → ordinaryHostResources G Hs=S → G≤Q → (∀v u,Hs v u→H v u) →
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
      ∃T,Good (i+1) T ∧ T⊆S ∧
        HasResourceDecomposition (ordinaryWheelResources (P:=Target⊔Reference) (F:=Fbad)
          (Hbase:=fun v u=>H v u ∨ Href v u) (r:=r)) (S\T)) →
    (∀T,Good L T→T⊆ordinaryRootResources W B) → HasFactorDecomposition Target Fs:=by
  intro Q H L Good hInitial hStep hTerminal
  letI:DecidableRel Q.Adj:=Classical.decRel _
  letI:∀v,DecidablePred (H v):=fun v u=>Classical.propDecidable (H v u)
  letI:∀u,DecidablePred (fun v=>H v u):=fun u v=>Classical.propDecidable (H v u)
  have hC:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→Target.Adj (f u x) (f u y):=
    fun u x y h=>(hRim u x y h).1
  obtain ⟨hcover',hBadFree,hBadPointwise⟩:=ordinary_forbidden_placement_completion_inputs
    Target Sample Reference Fbad Inner Fs C f Old E hpartition hcover
  have hPairRim:∀v∈Inner,∀w∈Inner,Q.Adj v w→Reference.Adj v w:=
    ordinary_required_cover_forces_reference_inner Target Sample Reference Protect
      (ordinaryEmbeddedComplements Fs C f) Inner hRef hProtect hcover'
  have hPairSpoke:∀v∈Inner,∀u∈Hubs,H v u→Href v u:=by
    intro v hv u hu hnot
    by_contra hn
    have hT:v∈ordinaryInnerSpokeTargets Inner Hubs Href u:=by
      simp [ordinaryInnerSpokeTargets,hu,hv,hn]
    obtain ⟨x,hx⟩:=hSpokeCover u v hT
    exact hnot ⟨x,hx⟩
  have hA:A⊆ordinaryHostResources Q H:=by
    apply ordinary_protected_reservoir_survives_complement Reference Target Fs C f Href A hAref hReserveTarget
    · intro u x y hxy
      have hh:=hRim u x y hxy
      exact ⟨hh.1,fun hr=>hh.2 (hReserveProtect hr)⟩
    · exact hAvoid
  obtain ⟨hbal,hdiv⟩:=ordinary_complement_remainder_balance Target hTarget Fs hFs C hsizeC f hC hCC
  have hbal':∀v,Q.degree v=2*(Finset.univ.filter (H v)).card:=by
    intro v
    have hh:=hbal v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hdiv':∀u,r∣(Finset.univ.filter (fun v=>H v u)).card:=by
    intro u
    have hh:=hdiv u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hP:∀v∈W,∀w∈W,Q.Adj v w→Reference.Adj v w:=by
    intro v hv w hw he
    exact hPairRim v (hW hv) w (hW hw) he
  have hH:∀v∈W,∀u∈B,H v u→Href v u:=by
    intro v hv u hu he
    exact hPairSpoke v (hW hv) u (hB hu) he
  let Hambient:Fin n→Fin q→Prop:=fun v u=>H v u ∨ Href v u
  have hRefP:Reference≤Target⊔Reference:=le_sup_right
  have hHref:∀v u,Href v u→Hambient v u:=fun _ _ h=>Or.inr h
  have hdecA':HasResourceDecomposition
      (ordinaryWheelResources (P:=Target⊔Reference) (F:=Fbad) (Hbase:=Hambient) (r:=r)) A:=
    ordinary_wheel_host_decomposition_lift hRefP hHref A hdecA
  have hdec:=ordinary_balanced_level_chain_completion_two_hosts Q (Target⊔Reference) Reference Fbad
    H Hambient Href r m hRefP hHref W B hm hbal' hdiv' hP hH A hA hdecA' hres
    L Good hInitial hStep hTerminal
  exact ordinary_complement_remainder_decomposition Target hTarget hr Fs hFs C hsizeC f hC hCC hdec
end Oberwolfach
