import SoporteDelGeneradorInverso
import MasaDeNacimientoDelParInverso
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section

theorem doble_borrado_sumado {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X z E)
    (leg : Legal X.physical) (a b j₂ j₃ : Bool) (hit : Mark n→Choice n→Vertex→Prop)
    (sub : ∀ u mov j,hit u mov j → consumeVertex mov j.1 j.2) :
    let row:=choices masas X (coloresDelPerfil n h p) (·⁻¹)
    (pesoDeUnaFuente n a*pesoDeUnaFuente n b)*masas.sum (soporteDeParejas X a b j₂ j₃)
      (fun u => meanN masas row (fun mov => deathsOn (diez u.1 u.2) (hit u mov)-1))≤
      45*(m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4)) := by
  intro row
  apply cota_de_suma_de_borrados (by omega) X leg
  intro u mem
  have cp:=((miembros_del_soporte X u.1 u.2 a b j₂ j₃).mp mem).1
  exact solapamiento_de_las_diez_lineas hn hh sp kp m1 zp hz z1 bal he ho X reg _ _ cp (hit u) (sub u)

/-- Each absent source adds a factor n to the number of summands.
It is the target weight that multiplies the sum over the pre-birth support. -/
theorem suma_de_error_de_nacimiento {n} (hn : 0<n) (X : State n) (leg : Legal X.physical)
    (primera v j₂ j₃ : Bool) (err : Mark n→ℝ≥0) (D : ℝ≥0)
    (cap : ∀ u∈soporteDeParejas X (if primera then false else v) (if primera then v else false) j₂ j₃,
      (n:ℝ≥0)^3*err u≤D) :
    pesoDeUnaFuente n v*masas.sum (soporteDeParejas X (if primera then false else v)
      (if primera then v else false) j₂ j₃) err≤D := by
  have np : (n:ℝ≥0)≠0 := by exact_mod_cast hn.ne'
  let a:=if primera then false else v
  let b:=if primera then v else false
  let l:=soporteDeParejas X a b j₂ j₃
  have qty:=cota_de_suma_de_borrados hn X leg a b j₂ j₃ (fun u => (n:ℝ≥0)*err u) D (by
    intro u hu
    rw [show (n:ℝ≥0)^2*(n*err u)=n^3*err u by ring]; exact cap u hu)
  have scalar : masas.sum l (fun u => (n:ℝ≥0)*err u)=n*masas.sum l err := by
    simpa only [mul_comm] using (show masas.sum l (fun u => err u*(n:ℝ≥0))=masas.sum l err*n from Cart.sum_scale masas l err (n:ℝ≥0))
  change (pesoDeUnaFuente n a*pesoDeUnaFuente n b)*masas.sum l (fun u => (n:ℝ≥0)*err u)≤D at qty
  rw [scalar,←mul_assoc] at qty
  have eq : (pesoDeUnaFuente n a*pesoDeUnaFuente n b)*(n:ℝ≥0)=pesoDeUnaFuente n v := by
    cases primera <;> simp [a,b,pesoDeUnaFuente,mul_assoc,mul_comm,mul_left_comm,np]
  rwa [eq] at qty

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.doble_borrado_sumado
#print axioms ArticuloA.Historias.suma_de_error_de_nacimiento
