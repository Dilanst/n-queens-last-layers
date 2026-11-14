import DelBlancoDeMallaAlPerfilContinuo
import IntegralInversaDelPerfilLleno
import BlancoDiscretoDelConteoInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil
def escalaDeLasFuentes (n h : ℕ) (p : FactoresContinuos) := (↑(n-h):ℝ)/Wfisico n p
def psiEnElCentro {n} (p : FactoresContinuos) (z : Cell n) := psiDiagonal p (medio n z.1.val) (medio n z.2.val)
def productoRCEnElCentro {n} (p : FactoresContinuos) (z : Cell n) :=
  (p.fila (medio n z.1.val):ℝ)*p.columna (medio n z.2.val)

theorem identidad_de_las_dos_esquinas {n h} (hn : 0<n) (p : FactoresContinuos) (u : Mark n) :
    (probDeLaCasilla h p u.1:ℝ)*probDeLaCasilla h p u.2*psiEnElCentro p (corners u).2 =
    escalaDeLasFuentes n h p*productoRCEnElCentro p (corners u).1*
      (probDeLaCasilla h p (corners u).2:ℝ)*factorEnCentros p (corners u).1 (corners u).2 := by
  simp only [probabilidad_fisica_por_peso p hn]
  rcases u with ⟨⟨r,j⟩,i,c⟩
  unfold escalaDeLasFuentes productoRCEnElCentro psiEnElCentro psiDiagonal factorEnCentros factorDelCruce
    pesoFisico pesoContinuo
  simp only [corners,factoresDelCruce]; ring

def sumaInversaDeLosCentros {n} (h : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) :=
  ∑ u : Mark n,w (corners u).1*((probDeLaCasilla h p u.1:ℝ)*probDeLaCasilla h p u.2*psiEnElCentro p (corners u).2)

theorem suma_inversa_por_cruces {n h} (hn : 0<n) (p : FactoresContinuos) (w : Cell n→ℝ) :
    sumaInversaDeLosCentros h p w=escalaDeLasFuentes n h p*
      ∑ z : Cell n,w z*productoRCEnElCentro p z*sumaSinFiltro h p z := by
  let v:=fun u : Mark n => w u.1*(escalaDeLasFuentes n h p*productoRCEnElCentro p u.1*
    (probDeLaCasilla h p u.2:ℝ)*factorEnCentros p u.1 u.2)
  let perm : Mark n≃Mark n := ⟨corners,corners,fun _ => rfl,fun _ => rfl⟩
  unfold sumaInversaDeLosCentros
  simp_rw [identidad_de_las_dos_esquinas hn]
  change (∑ u : Mark n,v (perm u))=_
  rw [Equiv.sum_comp perm v,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  unfold sumaSinFiltro
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _; dsimp only [v]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.identidad_de_las_dos_esquinas
#print axioms ArticuloA.Historias.suma_inversa_por_cruces
