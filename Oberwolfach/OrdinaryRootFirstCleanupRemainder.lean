module

public import Oberwolfach.OrdinaryRootFirstCleanupOutcome
public import Oberwolfach.OrdinaryRootCoverRemainderFacts
public import Oberwolfach.OrdinaryRootFirstPackingSubhost
public import Oberwolfach.OrdinaryRootFirstPackingDecomposition
public import Oberwolfach.OrdinaryHostDecompositions
public import Oberwolfach.OrdinaryWheelHostLift

@[expose] public section
/-! The actual cover, lifted packing and cleanup leave a balanced,
divisible host with no outside--outside resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_cleanup_remainder
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν D σ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    let K:=O.context;
    let R:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K;
    let S:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K;
    let Q₀:=Q\K.cover.rim;let H₀:=fun v u=>H v u∧¬K.cover.spokes v u;
    let Q₁:=Q₀\R;let H₁:=fun v u=>H₀ v u∧¬S v u;
    let C:=wheelFamilyRim O.cleanup.wheels;let J:=wheelFamilySpokes O.cleanup.wheels;
    let Q₂:=Q₁\C;let H₂:=fun v u=>H₁ v u∧¬J v u;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources C J) ∧
    (∀v,Q₂.degree v=2*(Finset.univ.filter (H₂ v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>H₂ v u)).card) ∧
    (∀v∉X,∀w∉X,¬Q₂.Adj v w) ∧
    (∀v∉X,∀u∉Z,¬H₂ v u) ∧
    (∀v∈T,∀w∉X,¬Q₂.Adj v w) ∧
    (∀v∈T,∀u∉Z,¬H₂ v u) ∧
    (∀u∈W,∀v∉X,¬H₂ v u):=by
  intro K R S Q₀ H₀ Q₁ H₁ C J Q₂ H₂
  have hs:=ordinary_root_first_packing_subhost Q F H X T Z W r η ell t K
  have hphys:ordinaryPhysicalGraph R S≤ordinaryPhysicalGraph Q₀ H₀:=by
    apply hs.1.trans
    rw [ordinary_unreserved_physical_graph]
    exact sdiff_le.trans sdiff_le
  have hR:R≤Q₀:=by intro v w hvw;exact hphys (v:=Sum.inl v) (w:=Sum.inl w) hvw
  have hS:∀v u,S v u→H₀ v u:=by intro v u hvu;exact hphys (v:=Sum.inl v) (w:=Sum.inr u) hvu
  have hc:=ordinary_root_cover_remainder_facts Q F H X T Z W r η ell hbal hdiv K.cover
  have hp:=ordinary_root_first_packing_decomposition Q F H X T Z W r η ell t K
  have hb:=ordinary_decomposition_remainder_balance Q₀ R H₀ S r hR hS (by
    intro v;convert hc.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by
    intro u;convert hc.2.1 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hp.2
  have hC:=wheelFamily_subhost O.cleanup.wheels
  have hb₂:=ordinary_decomposition_remainder_balance Q₁ C H₁ J r hC.1 hC.2 (by
    intro v;convert hb.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by
    intro u;convert hb.2 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) O.cleanup.decomposition
  have hhost:=wheelFamily_host_decomposition O.cleanup.wheels O.cleanup.disjoint
  have hhost':HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources C J):=
    ordinary_wheel_host_decomposition_lift (show Q₁≤Q from sdiff_le.trans sdiff_le)
      (fun _ _ h=>h.1.1) _ hhost
  refine ⟨hhost',?_,?_,O.cleanup.no_outer_rim,O.cleanup.no_outer_spoke,?_,?_,?_⟩
  · intro v
    convert hb₂.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    convert hb₂.2 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv w hw h
    exact hc.2.2.1 v hv w hw h.1.1
  · intro v hv u hu h
    exact hc.2.2.2.1 v hv u hu h.1.1
  · intro u hu v hv h
    exact hc.2.2.2.2 u hu v hv h.1.1
end Oberwolfach
