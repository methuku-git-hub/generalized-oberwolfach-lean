module

public import Oberwolfach.OrdinaryTriangleAssignedEndpointFailureBudget

@[expose] public section
/-! Name the common failure budget so it can be fixed after χ and before
the correction absorber and its finite thresholds are selected. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryTriangleFailureBudgetBeforeAbsorber (χ cap:ℝ) (N:ℕ):Prop :=
    ∀n:ℕ,N≤n→
    ∀ζ χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal:ℝ,
      ζ≤cap→χpair≤cap→χlist≤cap→χbal≤cap→χbd≤cap→χnbr≤cap→χpairR≤cap→χpath≤cap→
      χcol≤cap→χhub≤cap→χglobal≤cap→χlocal≤cap→
    ∀χinner χdeep χone χtwo χcut χhost χref χHub χendpoint:ℝ,
      χinner≤cap→χdeep≤cap→χone≤cap→χtwo≤cap→χcut≤cap→χhost≤cap→χref≤cap→χHub≤cap→χendpoint≤cap→
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Event:Ω→Prop),
    let loss0:=(((((((0+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    let loss:=loss0+χcol+χhub+χglobal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+χlocal;
    1-(loss+χdeep+χone+χtwo+χcut+χHub+χhost+χref)-χinner-χendpoint≤μ.probability Event→
    1-χ-1/(n:ℝ)^10≤μ.probability Event

theorem ordinary_triangle_failure_budget_before_absorber (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧ OrdinaryTriangleFailureBudgetBeforeAbsorber χ cap N :=by
  exact ordinary_triangle_assigned_endpoint_failure_budget χ hχ
end Oberwolfach
