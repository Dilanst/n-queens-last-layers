import DerivaFirmadaDeUnaRaiz
import ParametrosDeLasRaicesDirectas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita Corte
noncomputable section

def parteDeRaiz {n} (p : FactoresContinuos) (h T : ℕ) (z : Cell n) (j : Bool) (x : ℕ×State n) :=
  rootPart masas (·⁻¹) (2*n-1) ((2*n-1)-x.1) (T-x.1) z (cargaDeDestino h p z)
    (probDeLaCasilla h p) x.2 j

def constanteDirecta (m κ ζ C : ℝ≥0) :=
  let l:=piso κ ζ
  cotaDeRaiz (constanteUna l (techo m κ ζ) C) (m^4/l+4*(m^4/l^4)) (m^4/κ^4) ζ

theorem deriva_directa_con_el_perfil {n h t T : ℕ} {p : FactoresContinuos} {κ m ζ C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (tT : t<T) (tN : T≤2*n-1) (floor : ζ≤fraccionAntes n T)
    (bal : BalanceMalla n h p C) (mar : 2*(C:ℝ)≤κ*n)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ)
    (X : State n) (reg : Seguimiento h p X (fraccionAntes n t) E) (coh : coherent X)
    (vivo : X.failed=false) (z : Cell n) :
    let row:=kernel masas (coloresDelPerfil n h p) (·⁻¹) t X
    let R:=parteDeRaiz p h T z
    within masas (avg masas row (fun y => R false (t+1,y))+R true (t,X))
      (avg masas row (fun y => R true (t+1,y))+R false (t,X)) (constanteDirecta m κ ζ C*(E+1)/n) := by
  intro row R
  let N:=2*n-1
  let a:=N-(t+1)
  let d:=T-(t+1)
  have nn : 0<n := by omega
  have np : (n:ℝ≥0)≠0 := by exact_mod_cast nn.ne'
  have Np : (N:ℝ≥0)≠0 := by exact_mod_cast (show N≠0 by dsimp [N]; omega)
  have h₁ : a+1=N-t := by dsimp [a,N]; omega
  have h₂ : d+1=T-t := by dsimp [d]; omega
  let A:=region_del_estado hn hh sp kp m1 zp (fraccion_antes_del_horizonte tT.le floor)
    (fraccion_a_lo_sumo_uno hn t) bal he ho X reg
  have clock : (N:ℝ≥0)*A.z=(↑(a+1):ℝ≥0) := by
    change (N:ℝ≥0)*((↑(N-t):ℝ≥0)/N)=_; rw [h₁]; field_simp
  have span : (n:ℝ≥0)*A.c=N := by change (n:ℝ≥0)*((N:ℝ≥0)/n)=_; field_simp
  have remain : X.reals+X.virtuals≠0 := by
    intro no
    have bad:=reg.reloj; rw [no] at bad
    change (↑(0:ℕ):ℝ≥0)=(N:ℝ≥0)*A.z at bad
    rw [clock] at bad; have impossible : 0=a+1 := by exact_mod_cast bad
    omega
  have cap:=cargas_para_un_cruce hn sp kp bal mar z
  have one (u : ℝ≥0) : (n:ℝ≥0)*(u/n)=u := by field_simp
  have bd:=deriva_de_raiz_en_la_region A nn coh vivo remain E C (m^4/κ^4) ζ
    (le_of_eq (one E)) (le_of_eq (one (2*C))) (le_of_eq (one C)) t N a d
    (by dsimp [d,a,N]; omega) (by dsimp [a,N]; omega) (by dsimp [N]; omega) zp
    (piso_del_compensador hn tT floor) clock span z cap.1
    (fun e => (cargas_acotadas hn sp kp (0,0) e).2)
  dsimp only at bd
  rw [h₁,h₂] at bd
  exact bd

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_directa_con_el_perfil
