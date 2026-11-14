module

public import Oberwolfach.OrdinaryInitialCorrectedHostFacts
public import Oberwolfach.OrdinaryResourceRemovalExactBalance

@[expose] public section
/-! A decomposable reserved absorber survives as a removable resource set;
its removal leaves the initial corrected host balanced and divisible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_initial_corrected_reservoir_balance
    (P F JQ Pbase Fbase:SimpleGraph V) (JH Hbase:V→U→Prop) (π:Equiv.Perm V) (d r:ℕ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U))):
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    K⊆ordinaryHostResources Qcorr Hcorr→
    HasResourceDecomposition (ordinaryWheelResources (P:=Pbase) (F:=Fbase) (Hbase:=Hbase) (r:=r)) K→
    (∀v,Qcorr.degree v=2*(Finset.univ.filter (Hcorr v)).card)→
    (∀u,r∣(Finset.univ.filter (fun v=>Hcorr v u)).card)→
    G≤P ∧ Disjoint G F ∧ (∀v u,Hs v u→J v u) ∧
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card):=by
  intro R J Qcorr Hcorr G Hs hK hdec hbal hdiv
  have hf:=ordinary_initial_corrected_host_facts P F JQ JH π d j σ K
  have hb:=ordinary_resource_removal_exact_balance Qcorr Pbase Fbase Hcorr Hbase r (by convert hbal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by convert hdiv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) K hK hdec
  refine ⟨hf.1,hf.2.1,hf.2.2,?_,?_⟩
  · convert hb.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hb.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
