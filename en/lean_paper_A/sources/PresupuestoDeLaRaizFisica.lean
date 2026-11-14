import ErroresFisicosDeLosPatronesDirectos
import DerivaPorRaizE2
import SaltoDelCompensador
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita Corte
noncomputable section

def cotaDeRaiz (S D P ζ : ℝ≥0) :=
  let H := 8*P*ζ⁻¹^4
  16*((5+16*H)*S+(6+56*H)*D+6*ζ⁻¹^2+4*ζ⁻¹*H+56*ζ⁻¹^2*H)

theorem presupuesto_en_unidades_de_raiz (n : ℕ) (b g pair V a K S D H u E : ℝ≥0)
    (bnd : (n:ℝ≥0)^2*b≤S*(E+1)) (gnd : (n:ℝ≥0)^3*g≤S*(E+1))
    (pnd : (n:ℝ≥0)^2*pair≤D) (vnd : n*V≤2*H) (and' : n*a≤u) (knd : (n:ℝ≥0)^2*K≤H) :
    (n:ℝ≥0)*(masas.times 16 (fwCap masas n b g pair V)+
      masas.times 16 (masas.times n (occupiedCap masas a)+masas.times (n*n) (availCap masas a V K)))≤
    16*((5+16*H)*S+(6+56*H)*D+6*u^2+4*u*H+56*u^2*H)*(E+1) := by
  have ex : (1:ℝ≥0)≤E+1 := le_add_self
  have de : D≤D*(E+1) := by simpa only [mul_one] using (mul_le_mul_left' ex D)
  let B := (n:ℝ≥0)^2*b
  let J := (n:ℝ≥0)^2*pair
  let V' := (n:ℝ≥0)*V
  let u' := (n:ℝ≥0)*a
  let K' := (n:ℝ≥0)^2*K
  let G := (n:ℝ≥0)^3*g
  let adj := 6*u^2+4*u*H+28*u^2*(2*H)
  have ae : adj≤adj*(E+1) := by simpa only [mul_one] using (mul_le_mul_left' ex adj)
  calc
    _ = 16*((4*B+6*J+G+V'*(8*B+28*J))+(6*u'^2+4*u'*K'+28*u'^2*V')) := by
      simp only [fwCap,occupiedCap,availCap,times_m,ns_real,Nat.cast_mul,B,J,G,V',u',K']
      dsimp [masas]; ring
    _ ≤ 16*((4*(S*(E+1))+6*(D*(E+1))+S*(E+1)+2*H*(8*(S*(E+1))+28*(D*(E+1))))+adj) := by
      dsimp only [adj]
      gcongr <;> first | assumption | exact pnd.trans de
    _ ≤ 16*((4*(S*(E+1))+6*(D*(E+1))+S*(E+1)+2*H*(8*(S*(E+1))+28*(D*(E+1))))+adj*(E+1)) := by gcongr
    _ = _ := by dsimp only [adj]; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.presupuesto_en_unidades_de_raiz
