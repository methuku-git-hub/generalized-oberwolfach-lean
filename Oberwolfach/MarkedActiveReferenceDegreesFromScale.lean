module

public import Oberwolfach.MarkedActiveDomainSizeBounds
public import Oberwolfach.MarkedActiveReferenceGeometry

@[expose] public section

/-! Parent degree and reference hypotheses imply the actual degree,
two-step and domain-size inputs for the active packing theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A B Γ Color:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_active_reference_degrees_from_scale
    (f:A↪oV) (g:B↪U) (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (d r:ℕ) (hn:0<Fintype.card V)
    (rho gamma omega t kappa epsA deltaSp sRef tRef:ℝ)
    (hrho:0<rho) (hrho1:rho≤1) (hg:0<gamma) (ho:0<omega) (ho1:omega≤1)
    (ht:0≤t) (ht1:(r+4:ℝ)*t≤1) (hk:0≤kappa)
    (hk4:kappa≤1/4) (hkG:kappa≤gamma/4) (hkGR:kappa≤gamma*rho/16)
    (hkO:kappa≤omega/2) (heps:8*kappa≤epsA)
    (htwo:3*kappa≤gamma*(rho*(r+4:ℝ)*t/2)^2)
    (hdeg:∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))
    (hreg:∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤kappa*Fintype.card V)
    (hubs:omega*Fintype.card V≤(Fintype.card U:ℝ))
    (hRsize:((Finset.univ\Finset.univ.image f).card:ℝ)≤kappa*Fintype.card V)
    (hUsize:((Finset.univ\Finset.univ.image g).card:ℝ)≤kappa*Fintype.card V)
    (σ:RawMarkedOutcome V U Γ Color) (DR:SimpleGraph V) (a:Γ) (c:Color)
    (hstats:MarkedReferenceStatistics P π d a c (2*Fintype.card U/rho) kappa deltaSp gamma
      (rho*(r+4:ℝ)*t/2) ((rho*(r+4:ℝ)*t/2)/(r+4:ℝ)) sRef tRef σ)
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤kappa*Fintype.card V):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let p:=rho*(r+4:ℝ)*t/2
    let DA:=2*Fintype.card B/rho;
    (Fintype.card A:ℝ)/2≤DA∧DA≤2*Fintype.card A∧
    (omega/2)*Fintype.card A≤Fintype.card B∧Fintype.card B≤Fintype.card A∧
    (∀ mark x,
      |occurrenceDegree (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark=>e.val.1) x-
        (if mark then p/(r+4:ℝ) else p)*DA|≤epsA*Fintype.card A∧
      |occurrenceDegree (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark=>e.val.2) x-
        (if mark then p/(r+4:ℝ) else p)*DA|≤epsA*Fintype.card A)∧
    (∀ x y:A,x≠y→4*(gamma/8)*p^2*Fintype.card A≤
      ((Finset.univ.filter (fun z=>
        (∃ e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) false,e.val.1=x∧e.val.2=z)∧
        (∃ e:MarkedSampleArc (P.comap f) ρ (3*d) (fun a=>σA (Sum.inl a)) false,e.val.1=z∧e.val.2=y))).card:ℝ)):=by
  intro σA p DA
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hfcard:((Finset.univ\Finset.univ.image f).card:ℝ)=(Fintype.card V:ℝ)-Fintype.card A:=by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_image_of_injective _ f.injective,Finset.card_univ,
      Nat.cast_sub (Fintype.card_le_of_injective f f.injective)]
  have hgcard:((Finset.univ\Finset.univ.image g).card:ℝ)=(Fintype.card U:ℝ)-Fintype.card B:=by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_image_of_injective _ g.injective,Finset.card_univ,
      Nat.cast_sub (Fintype.card_le_of_injective g g.injective)]
  have hR:=hRsize;have hU:=hUsize
  rw [hfcard] at hR
  rw [hgcard] at hU
  obtain ⟨hA,hAhalf,hBhalf,hA0,hB0,_⟩:=marked_active_reference_geometry_from_scale
    (Fintype.card V) (Fintype.card U) (Fintype.card A) (Fintype.card B) omega kappa 1
    hn0 ho ho1 hk hk4 hkO (by norm_num) (by simpa using hkO) hR hU hubs
  have hAsize:0<Fintype.card A:=by exact_mod_cast hA0
  have hsize:=marked_active_domain_size_bounds f.toEmbedding g P hAsize rho gamma omega kappa
    hrho hrho1 hg.le ho.le hkG hk4 hdeg hreg hA hubs
    (hU.trans (mul_le_mul_of_nonneg_right hkGR hn0.le))
    (hU.trans (mul_le_mul_of_nonneg_right hkO hn0.le))
  have hp:0≤p:=by dsimp [p];positivity
  have htarget:=marked_degree_target_removed_hubs g r rho t hrho ht ht1
  have htarget':p*|(2*Fintype.card U/rho)-DA|≤(Finset.univ\Finset.univ.image g).card:=by
    change |p*(2*Fintype.card U/rho)-p*DA|≤(Finset.univ\Finset.univ.image g).card at htarget
    simpa only [←mul_sub,abs_mul,abs_of_nonneg hp] using htarget
  have hb: kappa*Fintype.card V+(Finset.univ\Finset.univ.image f).card+
      kappa*Fintype.card V+p*|(2*Fintype.card U/rho)-DA|≤epsA*Fintype.card A:=by
    have heps0:0≤epsA:=le_trans (by positivity) heps
    have h1:=mul_le_mul_of_nonneg_right heps hn0.le
    have h2:=mul_le_mul_of_nonneg_left hAhalf heps0
    nlinarith only [hRsize,hUsize,htarget',h1,h2]
  have htw:(Finset.univ\Finset.univ.image f).card+2*(kappa*Fintype.card V)≤gamma*p^2*Fintype.card V:=by
    have h1:=mul_le_mul_of_nonneg_right htwo hn0.le
    change 3*kappa*Fintype.card V≤gamma*p^2*Fintype.card V at h1
    nlinarith only [hRsize,h1]
  obtain ⟨hdegrees,htwosteps⟩:=marked_protected_active_reference_statistics f g π ρ hf P d r σ DR a c
    (2*Fintype.card U/rho) DA kappa epsA deltaSp gamma p sRef tRef (kappa*Fintype.card V)
    hg.le hp hstats hDR hb htw
  exact ⟨hsize.1,hsize.2.1,hsize.2.2.1,hsize.2.2.2,hdegrees,htwosteps⟩

end Oberwolfach
