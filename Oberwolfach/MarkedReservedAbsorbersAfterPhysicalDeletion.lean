module

public import Oberwolfach.MarkedFiniteAbsorbersAfterPhysicalDeletion
public import Oberwolfach.MarkedReservedTerminalAbsorberProperty
public import Oberwolfach.MarkedHostCountsPhysicalDeletionReal
public import Oberwolfach.MarkedFiniteAbsorberProperty
public import Oberwolfach.MarkedSampleCycleValidity
public import Oberwolfach.MarkedSampleHostInterfaces

@[expose] public section

/-! Construct finite absorbers in every later bounded physical deletion of
one fixed sampled host. The coefficients, domains and common-pair selectors
are inherited from the original host. The deletion tolerance is chosen
before the host, its sample and every later deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reserved_absorbers_after_physical_deletion
    (l:ℕ) (hl:2≤l) (ρ σ q₀ bc bp blo bhi B pstar:ℝ)
    (hρ:0<ρ) (hσ:0<σ) (hq:0<q₀) (hbc:0<bc) (hbp:0<bp)
    (hblo:0<blo) (hbhi:0<bhi) (hB:0<B) (hpstar:0<pstar) :
    ∃ ε ζ:ℝ,0<ε ∧ 0<ζ ∧ ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f d:ℕ,2≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],N≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (D τ A p k s₀:ℝ),
      (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      pstar≤p → pstar≤k → pstar≤s₀*s₀/((l+4:ℕ):ℝ) →
      p≤1 → k≤1 → s₀*s₀/((l+4:ℕ):ℝ)≤1 → q₀≤(s₀/((l+4:ℕ):ℝ))^2 →
    ∀ (weight:(Fin (l+4+1)→V)→ℝ),
      SuccessorSequenceWeightConditions P π (3*d) D τ A B weight →
      (∀ C:Fin (l+4+1)→V,SuccessorSequenceValid P π C→PermutationSeparated π (3*d) C→
        blo/(Fintype.card V:ℝ)^(l+4)≤weight C/(D*p^(l+4)*k*(s₀*s₀/((l+4:ℕ):ℝ))^(l+4)) ∧
        weight C/(D*p^(l+4)*k*(s₀*s₀/((l+4:ℕ):ℝ))^(l+4))≤bhi/(Fintype.card V:ℝ)^(l+4)) →
    ∀ (σBase:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
      (∀ v u,¬(H false v u∧H true v u)) →
      (∀ u u':U,u≠u'→∃ κ,CommonWitnessEstimates P π d l D p k s₀ (ε/2) (ε/2) (ε/2) bc bp weight σBase H κ u u') →
      MarkedHostExtensionCounts
        (fun e:MarkedSampleArc P π (3*d) (fun a=>σBase (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun a=>σBase (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
        (H false) (H true) π (3*d) l (ρ*Fintype.card V) (σ*Fintype.card V) →
    ∃ κ:U→U→V→Bool,
      (∀ u u':U,u≠u'→CommonWitnessEstimates P π d l D p k s₀ (ε/2) (ε/2) (ε/2) bc bp weight σBase H (κ u u') u u') ∧
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V) →
      (∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card V) →
    let σ':=rawMarkedDeleteRims σBase DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS;
    MarkedReservedTerminalAbsorberProperty
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
      (H' false) (H' true) π (3*d) l size a₀ b₀ e₀ f ε := by
  obtain ⟨ε,ζ,hε,hζ,hbase⟩:=marked_finite_absorbers_after_physical_deletion l hl
    ρ σ q₀ bc bp blo bhi B pstar hρ hσ hq hbc hbp hblo hbhi hB hpstar
  refine ⟨ε,ζ,hε,hζ,?_⟩
  intro size
  obtain ⟨a₀,b₀,hbase⟩:=hbase size
  refine ⟨2^(2*size^2)*a₀,2^(2*size^2)*b₀,2^(2*size^2)*(2*a₀^2+a₀*b₀),?_⟩
  intro f d hd
  obtain ⟨N,hN,hbase⟩:=hbase (f+2^(2*size^2)*(2*a₀^2+a₀*b₀)) d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P π D τ A p k s₀ hDlo hDhi hp hk hs hp1 hk1 hs1 hq0
    weight hw hweight σBase H htypes hwitness hcounts
  obtain ⟨κ,hκ,hfinite⟩:=hbase V U Γ Color hn P π D τ A p k s₀ hDlo hDhi hp hk hs hp1 hk1 hs1 hq0
    weight hw hweight σBase H htypes hwitness hcounts
  refine ⟨κ,hκ,?_⟩
  intro DR DS hrim hspoke σ' H'
  have hafter:=hfinite DR DS hrim hspoke
  exact marked_finite_to_reserved_terminal_absorber _ _ _ _ _ _ _
    (markedSampleArc_physical_injective P π (3*d) (fun a=>σ' (Sum.inl a)))
    (3*d) l size a₀ b₀ f ε hafter

end Oberwolfach
