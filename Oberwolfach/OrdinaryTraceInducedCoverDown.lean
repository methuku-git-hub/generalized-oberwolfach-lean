module

public import Oberwolfach.OrdinaryInducedProtectedCoverDown
public import Oberwolfach.OrdinaryProtectedTraceInvariant
public import Oberwolfach.OrdinaryVortexTargetDegree

@[expose] public section
/-! A protected trace places the actual current host in the preceding pair,
so a cover-down on that induced pair is an ambient next-level step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_trace_induced_coverdown
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:ℕ→Finset V) (Z W:ℕ→Finset U)
    (cost deepCost:ℕ→ℝ) (i r:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G F:SimpleGraph V) (Hs:V→U→Prop)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hbal:∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)
    (hXX:X (i+1)⊆X i) (hTX:T (i+1)⊆X i)
    (hZZ:Z (i+1)⊆Z i) (hWZ:W (i+1)⊆Z i)
    (hc0:0≤cost (i+1)) (hd0:0≤deepCost (i+1)):
    let VX:=↥(X i);let UZ:=↥(Z i);
    let Xloc:=ordinaryContainedTarget (X i) (X (i+1));
    let Tloc:=ordinaryContainedTarget (X i) (T (i+1));
    let Zloc:=ordinaryContainedTarget (Z i) (Z (i+1));
    let Wloc:=ordinaryContainedTarget (Z i) (W (i+1));
    OrdinaryProtectedHostCoverDownResult (G.induce ((X i):Set V)) (F.induce ((X i):Set V))
      (fun (v:VX) (u:UZ)=>Hs v.val u.val) Xloc Tloc Zloc Wloc r (cost (i+1)) (deepCost (i+1))→
    OrdinaryProtectedHostCoverDownResult G F Hs (X (i+1)) (T (i+1)) (Z (i+1)) (W (i+1)) r
      (cost (i+1)) (deepCost (i+1)):=by
  intro VX UZ Xloc Tloc Zloc Wloc hlocal
  have hparent:ordinaryHostResources G Hs⊆ordinaryRootResources (X i) (Z i):=by
    rw [hstate]
    have hh:=ordinary_protected_trace_terminal Q H X T Z W cost deepCost (i+1) (by omega) A htrace
    simpa only [Nat.add_sub_cancel] using hh
  have hh:=ordinary_induced_protected_coverdown G F Hs (X i) (Z i) Xloc Tloc Zloc Wloc r
    (cost (i+1)) (deepCost (i+1)) hc0 hd0 hparent hbal hdiv hlocal
  have hx:Xloc.image (⟨Subtype.val,Subtype.val_injective⟩:VX↪V)=X (i+1):=by
    convert ordinary_contained_target_image _ _ hXX using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have ht:Tloc.image (⟨Subtype.val,Subtype.val_injective⟩:VX↪V)=T (i+1):=by
    convert ordinary_contained_target_image _ _ hTX using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hz:Zloc.image (⟨Subtype.val,Subtype.val_injective⟩:UZ↪U)=Z (i+1):=by
    convert ordinary_contained_target_image _ _ hZZ using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hw:Wloc.image (⟨Subtype.val,Subtype.val_injective⟩:UZ↪U)=W (i+1):=by
    convert ordinary_contained_target_image _ _ hWZ using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  rw [hx,ht,hz,hw] at hh
  exact hh
end Oberwolfach
