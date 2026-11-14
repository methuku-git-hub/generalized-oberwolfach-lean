module

public import Oberwolfach.OrdinaryActualCertificateReferenceStaticAt

@[expose] public section
/-! The certificate's initial static geometry is retained after the parent
reference parameters and before the later matching spacing are fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryActualCertificateReferenceFirstStaticAt
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α:ℝ):Prop :=
    ∀(βparent ω bRoot BRoot hpack δ:ℝ),0<βparent→0<ω→0<bRoot→0<BRoot→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
      OrdinaryActualCertificateReferenceStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
end Oberwolfach
