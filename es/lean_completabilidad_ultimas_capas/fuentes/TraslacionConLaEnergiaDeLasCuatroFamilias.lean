import CotaLogaritmicaB35
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set
theorem comparacion_con_energia_de_las_fibras {v w : Fin 4→ℝ→ℝ} {K : ℝ}
    (cv : ∀ g,ContinuousOn (v g) (rangoF g)) (cw : ∀ g,ContinuousOn (w g) (rangoF g))
    (bv : ∀ g,∀ y∈rangoF g,Real.exp (v g y)≤K) (bw : ∀ g,∀ y∈rangoF g,Real.exp (w g y)≤K)
    (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) {d b y yt error E t B lam d₀ bMax : ℝ}
    (floor : 0<d₀) (coerc : 0<lam) (boundB : 0≤B) (db : |b|≤bMax)
    (orig : y*(d+b*cavidadFisica (fun g z=>Real.exp (w g z)) i s)=1)
    (moved : yt*(d+b*cavidadFisica (fun g z=>Real.exp (v g z)) i s)=1+error)
    (d1 : d₀≤d+b*cavidadFisica (fun g z=>Real.exp (w g z)) i s)
    (d2 : d₀≤d+b*cavidadFisica (fun g z=>Real.exp (v g z)) i s)
    (res : |error|≤2*B*|t|) (norm : E≤2*Real.sqrt 5*B*|t|)
    (anchor : lam*Real.sqrt (∑ g,energiaDeDiferencias v w g)≤E) :
    |yt-y|≤(2*B/d₀+2*Real.sqrt 15*bMax*K^3*B/(d₀^2*lam))*|t| :=
  comparacion_de_los_factores_trasladados floor coerc boundB ((Real.exp_pos _).le.trans (bv i s hs))
    db orig moved d1 d2 res norm anchor (estimacion_fisica_B35 cv cw bv bw i hs)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.comparacion_con_energia_de_las_fibras
