module

public import Oberwolfach.TypedMarkedPotentialDeletion
public import Oberwolfach.MarkedRetainedPotentialLoadRelabel

@[expose] public section
/-! Fixed typed potential loads remain controlled under simultaneous additions
and deletions, provided their actual typed incidence changes have bounded
degree. No containment between the two hosts is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}
  {H₀ Hₖ:V→U→Prop}

theorem marked_potential_load_after_host_modification
    (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ Hₖ→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R R':E⊕K→Prop) (H H':Bool→V→U→Prop) (d:ℝ) (hd:0≤d)
    (hout:∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d)
    (hin:∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d)
    (hHout:∀ j x,(∑ u,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d)
    (hHin:∀ j u,(∑ x,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d)
    (valid:((E⊕K)⊕(Bool×V×U))→Prop) (error:ℝ)
    (hbase:∀ root,valid root→|typedMarkedPotentialLoad w R H root-1|≤error) :
    ∀ root,valid root→|typedMarkedPotentialLoad w R' H' root-1|≤
      error+11*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  intro root hroot
  have hchange:=typedMarkedPotentialLoad_degree_stability hm hn hu w B hB hw R R' H H' d hd
    hout hin hHout hHin root
  have hold:=hbase root hroot
  have htri:=abs_add_le (typedMarkedPotentialLoad w R' H' root-typedMarkedPotentialLoad w R H root)
    (typedMarkedPotentialLoad w R H root-1)
  have heq : typedMarkedPotentialLoad w R' H' root-1 =
      (typedMarkedPotentialLoad w R' H' root-typedMarkedPotentialLoad w R H root)+
      (typedMarkedPotentialLoad w R H root-1) := by ring
  rw [heq]
  linarith
theorem marked_potential_load_uniform_host_modification
    (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel tail head ktail khead m π b H₀ Hₖ→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R:E⊕K→Prop) (H:Bool→V→U→Prop)
    (valid:((E⊕K)⊕(Bool×V×U))→Prop) (error:ℝ)
    (hbase:∀ root,valid root→|typedMarkedPotentialLoad w R H root-1|≤error) :
    ∀ (R':E⊕K→Prop) (H':Bool→V→U→Prop) (d:ℝ), 0≤d →
    (∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d) →
    (∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d) →
    (∀ j x,(∑ u,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d) →
    (∀ j u,(∑ x,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d) →
    ∀ root,valid root→|typedMarkedPotentialLoad w R' H' root-1|≤
      error+11*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  intro R' H' d hd hout hin hHout hHin
  exact marked_potential_load_after_host_modification hm hn hu w B hB hw R R' H H' d hd
    hout hin hHout hHin valid error hbase
end Oberwolfach
