import OscilacionEspacialDelPeso
import MasaRealDelPerfil
import MasaVirtualDelPerfil
import DelCosteAlPrimerOrden
open Set MeasureTheory
open scoped Interval NNReal
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2
noncomputable section

structure PerfilKL (n h : ℕ) (p : FactoresContinuos) (κ M L b m₀ : ℝ) : Prop where
  espacial : ControlEspacial p κ M L
  kpos : 0<κ
  k1 : κ≤1
  m1 : 1≤M
  lpos : 0≤L
  bpos : 0<b
  mpos : 0<m₀
  extremoD : p.diagonal (-1)=1
  extremoA : p.anti 0=1
  fila : (∫ y in (0:ℝ)..1,(p.fila y:ℝ))=1
  columna : (∫ y in (0:ℝ)..1,(p.columna y:ℝ))=1
  diag : (n:ℝ)*(∫ y in (-1:ℝ)..1,(p.diagonal y:ℝ))=(n:ℝ)+(h:ℝ)
  anti : (n:ℝ)*(∫ y in (0:ℝ)..2,(p.anti y:ℝ))=(n:ℝ)+(h:ℝ)
  masa : integralTablero (pesoContinuo p)=(↑(n-h):ℝ)/((n:ℝ)*b)
  minimoMasa : m₀ ≤ integralTablero (pesoContinuo p)

def amplitudPerfil (κ M : ℝ) := constanteDifusion (κ^4) (M^4) κ (M^4)
def errorPerfil (κ M L m₀ : ℝ) :=
  2*(4*M^3*L)/m₀+4*(2*L+2)+6*(L/κ)

theorem masa_log_real {n h p κ M L b m₀} (src : PerfilKL n h p κ M L b m₀)
    (hn : 0<n) (hq : 0<n-h) (x : ℝ≥0) (xp : 0<x)
    (positive : 0<Wreal n (sameColors (pesosMalla n x p))) :
    (↑(n-h):ℝ)*(Real.log (Wreal n (sameColors (pesosMalla n x p)))-
      (Real.log n+Real.log (n-h:ℕ)+(-Real.log (b/(x:ℝ)^2))))≤2*(4*M^3*L)/m₀ := by
  have mp : 0≤M := le_trans zero_le_one src.m1
  apply log_Wreal_del_perfil n _ hn hq (Nat.sub_le _ _) x xp p (4*M^3*L) b m₀
    (mul_nonneg (by positivity) src.lpos) src.bpos src.mpos src.minimoMasa src.masa positive
  · intro r hr i hi c hc
    simpa only [sub_self,abs_zero,add_zero] using variacion_del_peso src.espacial src.lpos r i c c hr hi hc hc
  · intro r hr c hc j hj
    simpa only [sub_self,abs_zero,zero_add] using variacion_del_peso src.espacial src.lpos r r c j hr hr hc hj

theorem masas_virtuales {n h p κ M L b m₀} (src : PerfilKL n h p κ M L b m₀)
    (hn : 2≤n) (x : ℝ≥0) (x1 : (x:ℝ)≤1) (cuota : (x:ℝ)*(n:ℝ)=(h:ℝ)) :
    ∀ j,sumasVirtuales n (sameColors (pesosMalla n x p)) j-((n:ℝ)+h-1)≤2*L+2 :=
  cotas_cuatro_sumas n h hn x x1 cuota p κ L src.lpos src.espacial.R src.espacial.C src.espacial.D
    src.espacial.A src.extremoD src.extremoA src.fila src.columna src.diag src.anti

theorem producto_log {n h p κ M L b m₀} (src : PerfilKL n h p κ M L b m₀)
    (hn : 0<n) (x : ℝ≥0) (xp : 0<x) :
    (n:ℝ)*entropiaDeFactores p x-(∑ i,∑ j : Indice n,Real.log (factores (pesosMalla n x p) i j))≤6*(L/κ) :=
  (abs_le.mp (error_del_producto_de_pesos n hn p x xp κ L src.kpos src.lpos src.espacial.R src.espacial.C
    src.espacial.D src.espacial.A src.extremoD src.extremoA)).2

theorem capa_positiva_si_hay_solucion {n h : ℕ} (hn : h≤n) (sol : 0<count n n) : 0<count n (n-h) := by
  have pos := Nat.mul_pos (Nat.choose_pos hn) sol
  have rhs := lt_of_lt_of_le pos (Capas.retirada_binomial n h hn)
  by_contra! he
  rw [Nat.eq_zero_of_le_zero he,Nat.mul_zero] at rhs
  exact (Nat.lt_irrefl _) rhs
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_log_real
#print axioms ArticuloA.Historias.masas_virtuales
#print axioms ArticuloA.Historias.producto_log
