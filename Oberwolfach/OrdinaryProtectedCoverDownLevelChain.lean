module

public import Oberwolfach.OrdinaryProtectedResourceLevelStep
public import Oberwolfach.OrdinaryBalancedLevelChain

@[expose] public section
/-! A conflict-respecting wheel cover-down at each level supplies the exact
resource steps of the balanced chain. The analytic invariant and absorber
remain explicit hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_coverdown_level_chain
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r m:ℕ)
    (W:Finset V) (B:Finset U) (hsize:W.card+B.card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hQP:Q≤P) (hHbase:∀v u,H v u→Hbase v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources Q H)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources W B →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (X Tdeep:ℕ→Finset V) (Z Wdeep:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (Good:ℕ→Finset (Sym2 V⊕(V×U))→Prop)
    (hInitial:Good 0 (ordinaryHostResources Q H\A))
    (hCover:∀i<L,∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      Good i S→ ordinaryHostResources G Hs=S→G≤Q→(∀v u,Hs v u→H v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownResult G F Hs (X i) (Tdeep i) (Z i) (Wdeep i) r (cost i) (deepCost i))
    (hAdvance:∀i<L,∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      Good i S→ ordinaryHostResources G Hs=S→
      ∀(D:SimpleGraph V) (E:V→U→Prop),D≤G→(∀v u,E v u→Hs v u)→
      let Gnext:=G\D;let Hnext:=fun v u=>Hs v u∧¬E v u;
      ordinaryHostResources Gnext Hnext⊆ordinaryRootResources (X i) (Z i)→
      (∀v,Gnext.degree v=2*(Finset.univ.filter (Hnext v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hnext v u)).card)→
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤cost i)→
      (∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph D E (Tdeep i) (Wdeep i)) (ordinaryInnerVertices (X i) (Z i))).degree w:ℝ)≤deepCost i)→
      Disjoint (ordinaryPhysicalGraph D E) (ordinaryDeepBlocker (Tdeep i) (Wdeep i))→
      Good (i+1) (ordinaryHostResources Gnext Hnext))
    (hTerminal:∀T,Good L T→T⊆ordinaryRootResources W B):
    HasOrdinaryWheelDecomposition Q H r:=by
  apply ordinary_balanced_level_chain_completion Q P F H Hbase r m W B hsize hbal hdiv
    (fun _ _ _ _ h=>hQP h) (fun v _ u _ h=>hHbase v u h) A hA hdecA hres L Good hInitial
  · intro i hi S G Hs hgood hEq hG hHs hb hd
    have hstep:=hCover i hi S G Hs hgood hEq hG hHs hb hd
    obtain ⟨T,hTS,hroot,hdec,Gnext,Hnext,hnext,hnb,hnd,D,E,hDG,hEH,hDGnext,hEHnext,hcost,hdeepcost,hdeep⟩:=
      ordinary_protected_resource_level_step P G F Hbase Hs (X i) (Tdeep i) (Z i) (Wdeep i) r (cost i) (deepCost i)
        (hG.trans hQP) (fun v u h=>hHbase v u (hHs v u h)) hstep
    subst Gnext
    subst Hnext
    have hroot':ordinaryHostResources (G\D) (fun v u=>Hs v u∧¬E v u)⊆ordinaryRootResources (X i) (Z i):=by
      rw [hnext]
      exact hroot
    have hnb':∀v,(G\D).degree v=2*(Finset.univ.filter (fun u=>Hs v u∧¬E v u)).card:=by
      convert hnb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hnd':∀u,r∣(Finset.univ.filter (fun v=>Hs v u∧¬E v u)).card:=by
      convert hnd using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hgood':Good (i+1) T:=by
      rw [←hnext]
      exact hAdvance i hi S G Hs hgood hEq D E hDG hEH hroot' hnb' hnd' hcost hdeepcost hdeep
    have hdec':HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) (S\T):=by
      rw [←hEq]
      exact hdec
    exact ⟨T,hgood',by rw [←hEq];exact hTS,hdec'⟩
  · exact hTerminal
end Oberwolfach
