import DerivadasDeLosPesosDelReloj
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

theorem ampliar_paso {x v x' d A B : ℝ} (h : PasoDelReloj x v x' d A) (dp : 0≤d) (ab : A≤B) :
    PasoDelReloj x v x' d B :=
  ⟨h.old.trans ab,h.new.trans ab,h.slope.trans ab,h.change.trans (mul_le_mul_of_nonneg_right ab dp),
   h.error.trans (mul_le_mul_of_nonneg_right ab (sq_nonneg _))⟩

theorem escalar_paso {x v x' d B : ℝ} (h : PasoDelReloj x v x' d B) (s : ℝ) :
    PasoDelReloj (s*x) (s*v) (s*x') d (|s| *B) := by
  have mult {u A : ℝ} (bound : |u|≤A) := mul_le_mul_of_nonneg_left bound (abs_nonneg s)
  constructor
  · rw [abs_mul]; exact mult h.old
  · rw [abs_mul]; exact mult h.new
  · rw [abs_mul]; exact mult h.slope
  · rw [←mul_sub,abs_mul,mul_assoc]; exact mult h.change
  · rw [show s*x'-s*x-d*(s*v)=s*(x'-x-d*v) by ring,abs_mul,mul_assoc]; exact mult h.error

def normaDelReloj (ζ : ℝ) := (max 1 ζ⁻¹)^3
def normaFuenteDelReloj (ζ : ℝ) := 81*(normaDelReloj ζ)^4
def normaDestinoDelReloj (ζ : ℝ) := 3*normaDelReloj ζ

theorem pasos_fuente_y_destino {d ζ y z : ℝ} (dp : 0≤d) (dy : d≤y) (yt : y≤1) (zp : 0<ζ) (cut : ζ≤z-d) :
    PasoDelReloj (y/z^4) (-1/z^4+4*y/z^5) ((y-d)/(z-d)^4) d (normaFuenteDelReloj ζ) ∧
    PasoDelReloj (y/z) (-1/z+y/z^2) ((y-d)/(z-d)) d (normaDestinoDelReloj ζ) := by
  have i:=paso_del_reciproco dp zp cut
  have yb:=paso_del_numerador dp dy yt
  have sq:=producto_de_pasos dp i i
  have quart:=producto_de_pasos dp sq sq
  have four:=producto_de_pasos dp yb quart
  have one:=producto_de_pasos dp yb i
  constructor
  · convert four using 1 <;> simp only [normaFuenteDelReloj,normaDelReloj,div_eq_mul_inv,←inv_pow] <;> ring
  · convert one using 1 <;> dsimp [normaDestinoDelReloj,normaDelReloj] <;> ring

/-- Derivative in the forward direction of the normalized time. -/
def velocidadCuatro (x v : Fin 4→ℝ) :=
  Inversa.productRule (x 0) (x 1) (x 2) (x 3) (v 0) (v 1) (v 2) (v 3)

theorem multiplicar_cuatro_pasos {d : ℝ} (dp : 0≤d) (x v x' B : Fin 4→ℝ)
    (one : ∀ i,PasoDelReloj (x i) (v i) (x' i) d (B i)) :
    PasoDelReloj (x 0*x 1*x 2*x 3) (velocidadCuatro x v) (x' 0*x' 1*x' 2*x' 3) d
      (27*(B 0*B 1*B 2*B 3)) := by
  have both:=producto_de_pasos dp (producto_de_pasos dp (producto_de_pasos dp (one 0) (one 1)) (one 2)) (one 3)
  convert both using 1 <;> dsimp [velocidadCuatro,Inversa.productRule] <;> ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ampliar_paso
#print axioms ArticuloA.Historias.escalar_paso
#print axioms ArticuloA.Historias.pasos_fuente_y_destino
#print axioms ArticuloA.Historias.multiplicar_cuatro_pasos
