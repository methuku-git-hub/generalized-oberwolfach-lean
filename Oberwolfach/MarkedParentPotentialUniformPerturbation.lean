module

public import Oberwolfach.MarkedReferenceParentPotentialAfterChanges

@[expose] public section
/-! A fixed positive margin controls all original root-omitted loads
after any sufficiently small realised typed change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_parent_potential_uniform_perturbation
    (r:ℕ) (κ B pstar:ℝ) (hκ:0<κ) (hB:0≤B) (hpstar:0<pstar):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (rho t τ A eps:ℝ)
      (weight:(Fin (r+4+1)→V)→ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (c:Color)
      (σ σ':RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0<Fintype.card V → Fintype.card U≤Fintype.card V →
    (∀ e,¬(rawMarkedPairRims P π d σ e↔rawMarkedPairRims P π d σ' e)→markedPairPhysical π e∈FR.edgeFinset) →
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V) → eps≤κ/8 →
    let DRef:=2*Fintype.card U/rho
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let sRef:=(r+4:ℝ)*t
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd (r+4) π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(DRef*pRef^(r+4)*kRef*sRef^(r+4));
    (Fintype.card V:ℝ)/2≤DRef → DRef≤2*Fintype.card V →
    pstar≤pRef → pstar≤kRef → pstar≤sRef → pRef≤1 → kRef≤1 → sRef≤1 →
    SuccessorSequenceWeightConditions P π (3*d) DRef τ A B weight →
    (∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a c root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤eps) →
    ∀ root,rawMarkedWheelMarginal P π d pRef kRef q s a c root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ') H' root-1|≤κ/4 := by
  let C:=33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))
  have hC:0≤C:=by dsimp [C];positivity
  let ζcap:=κ/(8*(C+1))
  have hcap:0<ζcap:=by dsimp [ζcap];positivity
  have hcapC:ζcap*(8*(C+1))=κ:=by dsimp [ζcap];field_simp
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζle V U Γ Color _ _ _ _ _ _ P π d rho t τ A eps weight q s a c σ σ' H H' FR FS
    hn hu hR hS hFR hFS heps DRef pRef kRef sRef seed hDlo hDhi hp hk hs hp1 hk1 hs1 hw hbase
  have hzC:C*ζ≤C*ζcap:=mul_le_mul_of_nonneg_left hζle hC
  have hbudget:eps+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤κ/4 := by
    change eps+C*ζ≤κ/4
    nlinarith [mul_nonneg hC hcap.le]
  exact marked_reference_parent_potential_after_changes r P π d hn hu rho t τ A B pstar eps ζ κ
    hζ hB hpstar weight q s a c σ σ' H H' FR FS hR hS hFR hFS
    hDlo hDhi hp hk hs hp1 hk1 hs1 hw hbase hbudget
end Oberwolfach
