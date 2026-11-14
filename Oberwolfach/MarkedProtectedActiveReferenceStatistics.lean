module

public import Oberwolfach.MarkedPhysicalDegreeTransfer
public import Oberwolfach.MarkedProtectedActiveTwoStep
public import Oberwolfach.MarkedReferenceStatistics

@[expose] public section

/-! Reference statistics give the actual active degree and two-step
hypotheses. The two-step bound is for every distinct pair of roots.
The change of degree target is explicitly charged to removed hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem markedPhysicalRim_pos_iff_one (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (mark:Bool) (x y:V):
    0<markedPhysicalRim P π b σ mark x y↔markedPhysicalRim P π b σ mark x y=1:=by
  unfold markedPhysicalRim permutationSeparatedMatrix markedPhysicalOrientation
  split_ifs <;> simp_all <;> split_ifs <;> simp_all

theorem marked_protected_active_reference_statistics
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d r:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V) (a:Γ) (c:Color)
    (D DA ε εA δsp γ p s t δ:ℝ) (hγ:0≤γ) (hp:0≤p)
    (hstats:MarkedReferenceStatistics P π d a c D ε δsp γ p (p/(r+4:ℝ)) s t σ)
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤δ)
    (hdeg:ε*Fintype.card V+(Finset.univ\Finset.univ.image f).card+δ+p*|D-DA|≤εA*Fintype.card W)
    (htwo:(Finset.univ\Finset.univ.image f).card+2*δ≤γ*p^2*Fintype.card V):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset);
    (∀ mark x,
      |occurrenceDegree (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark=>e.val.1) x-
        (if mark then p/(r+4:ℝ) else p)*DA|≤εA*Fintype.card W∧
      |occurrenceDegree (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark=>e.val.2) x-
        (if mark then p/(r+4:ℝ) else p)*DA|≤εA*Fintype.card W)∧
    (∀ x y:W,x≠y→4*(γ/8)*p^2*Fintype.card W≤
      ((Finset.univ.filter (fun z=>
        (∃ e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) false,e.val.1=x∧e.val.2=z)∧
        (∃ e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) false,e.val.1=z∧e.val.2=y))).card:ℝ)):=by
  intro σA
  have ht (mark:Bool):0≤(if mark then p/(r+4:ℝ) else p)∧(if mark then p/(r+4:ℝ) else p)≤p:=by
    cases mark
    · exact ⟨hp,le_rfl⟩
    · constructor
      · positivity
      · exact div_le_self hp (by have h:0≤(r:ℝ):=Nat.cast_nonneg r;linarith)
  have hdeg0:=marked_protected_active_degrees f g π ρ hf P d σ DR
    (fun mark=>(if mark then p/(r+4:ℝ) else p)*D)
    (fun mark=>(if mark then p/(r+4:ℝ) else p)*DA) (ε*Fintype.card V) δ hDR
    (by intro mark x;simpa only [←Nat.cast_sum] using (hstats.1.1 mark x).1)
    (by intro mark x;simpa only [←Nat.cast_sum] using (hstats.1.1 mark x).2)
  constructor
  · intro mark x
    have htarget:|(if mark then p/(r+4:ℝ) else p)*D-(if mark then p/(r+4:ℝ) else p)*DA|≤p*|D-DA|:=by
      rw [←mul_sub,abs_mul,abs_of_nonneg (ht mark).1]
      exact mul_le_mul_of_nonneg_right (ht mark).2 (abs_nonneg _)
    have hh:=hdeg0 mark x
    constructor <;> linarith only [hh.1,hh.2,htarget,hdeg]
  · intro x y hxy
    have hlow:=marked_protected_active_two_step f g π ρ hf P d σ DR false δ
      (3/2*γ*p^2*Fintype.card V) hDR (by
        intro x y hxy
        simpa only [markedPhysicalRim_pos_iff_one] using hstats.1.2 x y hxy) x y hxy
    have hn:(Fintype.card W:ℝ)≤Fintype.card V:=Nat.cast_le.mpr (Fintype.card_le_of_injective f f.injective)
    have hh:=mul_le_mul_of_nonneg_left hn (by positivity:0≤4*(γ/8)*p^2)
    linarith only [hlow,htwo,hh]

theorem marked_degree_target_removed_hubs (g:Z↪U) (r:ℕ) (rho t:ℝ)
    (hrho:0<rho) (ht:0≤t) (ht1:(r+4:ℝ)*t≤1):
    |(rho*(r+4:ℝ)*t/2)*(2*Fintype.card U/rho)-
      (rho*(r+4:ℝ)*t/2)*(2*Fintype.card Z/rho)|≤(Finset.univ\Finset.univ.image g).card:=by
  have hc:(Finset.univ\Finset.univ.image g).card=Fintype.card U-Fintype.card Z:=by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Finset.card_image_of_injective _ g.injective,Finset.card_univ]
  have hn:Fintype.card Z≤Fintype.card U:=Fintype.card_le_of_injective g g.injective
  rw [hc,Nat.cast_sub hn]
  have he:(rho*(r+4:ℝ)*t/2)*(2*Fintype.card U/rho)-
      (rho*(r+4:ℝ)*t/2)*(2*Fintype.card Z/rho)=
      ((r+4:ℝ)*t)*((Fintype.card U:ℝ)-Fintype.card Z):=by
    field_simp [ne_of_gt hrho]
    <;> ring
  rw [he,abs_of_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (Nat.cast_le.mpr hn)))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (sub_nonneg.mpr (Nat.cast_le.mpr hn))

end Oberwolfach
