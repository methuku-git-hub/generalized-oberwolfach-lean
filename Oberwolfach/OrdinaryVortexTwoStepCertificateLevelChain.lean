module

public import Oberwolfach.OrdinaryUniformProtectedBalanceLevelChain
public import Oberwolfach.OrdinaryWheelLikelySeparateCostsCertificate
public import Oberwolfach.VortexExtended

@[expose] public section
/-! Two-step vortex windows are empty: local likely-event certificates can
therefore feed the actual uniform-history and absorber chain directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_vortex_two_step_certificate_level_chain
    (P Q F:SimpleGraph V) (H Hbase:V→U→Prop) (r m D vsize:ℕ) (β ε:ℝ)
    (Vort:Vortex U P D β ε vsize) (L:ℕ) (hL:0<L)
    (hsize:(Vort.extendedVertices L).card+(Vort.extendedIndices L).card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hQP:Q≤P) (hHbase:∀v u,H v u→Hbase v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources Q H)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources (Vort.extendedVertices L) (Vort.extendedIndices L)→
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m→
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card)→
      G'≤P→(∀v u,H' v u→Hbase v u)→
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A)
    (cost deepCost:ℕ→ℝ):
    let Q₀:=Q\ordinaryResourceRim Q A;
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈A);
    let X:=fun t=>Vort.extendedVertices (t+1);let T:=fun t=>Vort.extendedVertices (t+2);
    let Z:=fun t=>Vort.extendedIndices (t+1);let W:=fun t=>Vort.extendedIndices (t+2);
    let I:=fun t=>Vort.extendedVertices (t+2);let Parent:=fun t=>Vort.extendedVertices (t+1);
    let J:=fun t=>Vort.extendedIndices (t+2);let window:=fun t=>Finset.Icc (t+3-2) t;
    (∀i<L,∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Q₀ H₀ X T Z W cost deepCost r i L S I Parent J window
        (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=S→G≤Q→(∀v u,Hs v u→H v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryWheelLikelySeparateCostsCertificate G F Hs (X i) (T i) (Z i) (W i) r (cost i) (deepCost i))→
    HasOrdinaryWheelDecomposition Q H r:=by
  intro Q₀ H₀ X T Z W I Parent J window hstep
  have hlast:L-1+1=L:=by omega
  apply ordinary_uniform_protected_balance_level_chain Q P F H Hbase r m
    (Vort.extendedVertices L) (Vort.extendedIndices L) hsize hbal hdiv hQP hHbase A hA hdecA hres L hL
    X T Z W cost deepCost I Parent J window (fun _ _=>0) (fun _ _=>0)
    (by dsimp [X];rw [hlast]) (by dsimp [Z];rw [hlast])
  intro i hi S G Hs hist hstate hG hHs hGB hGD
  obtain ⟨D',E',hD,hE,hdec,hroot,hnextbal,hnextdiv,hcost,hdeepcost,havoid⟩:=
    ordinary_wheel_likely_separate_costs_certificate_coverdown G F Hs (X i) (T i) (Z i) (W i) r (cost i) (deepCost i)
      (hstep i hi S G Hs hist hstate hG hHs hGB hGD)
  refine ⟨D',E',hD,hE,hdec,hroot,hnextbal,hnextdiv,hcost,hdeepcost,havoid,?_,?_⟩
  · intro target _ hmem
    have hh:=Finset.mem_Icc.mp hmem
    omega
  · intro target _ hmem
    have hh:=Finset.mem_Icc.mp hmem
    omega
end Oberwolfach
