module

public import Oberwolfach.OrdinaryShiftedRimDeletion
public import Oberwolfach.TypedMarkedPotentialDegreeStability

@[expose] public section
/-! Deleting bounded-degree physical rim edges changes every marked-wheel
root load by a controlled amount, with the seed weights fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_marked_load_deletion_stability
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (σ:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color)
    (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀x,(D.degree x:ℝ)≤δ)
    (root:((V×V)⊕(V×V))⊕(Bool×V×U)):
    |typedMarkedPotentialLoad w (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset))
        (rawMarkedPairSpokes π d σ g j) root-
      typedMarkedPotentialLoad w (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root|≤
      22*((m:ℝ)+1)^4*B*δ/Fintype.card V :=by
  let R:=ordinaryShiftedPairRims P π d σ
  let R':=ordinaryShiftedPairRims P π d (rawMarkedDeleteRims σ D.edgeFinset)
  let H:=rawMarkedPairSpokes π d σ g j
  obtain ⟨hout,hin⟩:=ordinary_shifted_rim_deletion_incidence P π d σ D δ hD
  have hzout:∀a x,(∑u,bipAdj (fun x u=>¬(H a x u↔H a x u)) x u)≤2*δ:=by
    intro a x
    simp only [iff_self,not_true,bipAdj,ite_false,Finset.sum_const_zero]
    positivity
  have hzin:∀a u,(∑x,bipAdj (fun x u=>¬(H a x u↔H a x u)) x u)≤2*δ:=by
    intro a u
    simp only [iff_self,not_true,bipAdj,ite_false,Finset.sum_const_zero]
    positivity
  cases root with
  | inl e=>
    have hh:=typedMarkedPotentialLoad_rim_degree_stability hm hn hu w B hB hw R R' H H (2*δ) (by positivity) hout hin hzout hzin e
    convert hh using 1 <;> (try ring) <;> congr! 3
  | inr a=>
    obtain ⟨mark,v,u⟩:=a
    have hh:=typedMarkedPotentialLoad_spoke_degree_stability hm hn w B hB hw R R' H H (2*δ) (by positivity) hout hin hzout hzin mark v u
    have hscale:0≤((m:ℝ)+1)^4*B*δ/(Fintype.card V:ℝ):=by positivity
    have hh':|typedMarkedPotentialLoad w R' H (Sum.inr (mark,v,u))-typedMarkedPotentialLoad w R H (Sum.inr (mark,v,u))|≤
        10*((m:ℝ)+1)^4*B*δ/Fintype.card V:=by convert hh using 1 <;> ring
    apply hh'.trans
    have hb:10*(((m:ℝ)+1)^4*B*δ/(Fintype.card V:ℝ))≤22*(((m:ℝ)+1)^4*B*δ/(Fintype.card V:ℝ)):=by nlinarith
    convert hb using 1 <;> ring
end Oberwolfach
