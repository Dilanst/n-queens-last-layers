import CalculoDeUnPasoEnLasCuatroMarcas
import PesosAdjuntosAntesDelCorte
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def factorTemporal (src b : Bool) (y z : ℝ) : ℝ :=
  if src then (if b then 1 else y/z^4) else (if b then y/z else 1)
def velocidadTemporal (src b : Bool) (y z : ℝ) : ℝ :=
  if src then (if b then 0 else -1/z^4+4*y/z^5) else (if b then -1/z+y/z^2 else 0)
def factoresPatron (f : Bool→Bool→ℝ) (t : CuatroMarcas) : Fin 4→ℝ :=
  ![f true t.1,f true t.2.1,f false t.2.2.1,f false t.2.2.2]
def formaTemporal (y z : ℝ) (t : CuatroMarcas) :=
  monoCuatro (fun b => factorTemporal true b y z) (fun b => factorTemporal true b y z)
    (fun b => factorTemporal false b y z) (fun b => factorTemporal false b y z) t
def pendienteTemporal (y z : ℝ) (t : CuatroMarcas) :=
  velocidadCuatro (factoresPatron (fun s b => factorTemporal s b y z) t)
    (factoresPatron (fun s b => velocidadTemporal s b y z) t)
def cotaRelojComun (ζ : ℝ) := max 1 (max (normaFuenteDelReloj ζ) (normaDestinoDelReloj ζ))

theorem reloj_de_las_dieciseis_marcas {d ζ y z : ℝ} (dp : 0≤d) (dy : d≤y) (yt : y≤1) (zp : 0<ζ)
    (cut : ζ≤z-d) (t : CuatroMarcas) :
    PasoDelReloj (formaTemporal y z t) (pendienteTemporal y z t) (formaTemporal (y-d) (z-d) t) d
      (27*(cotaRelojComun ζ)^4) := by
  let B:=cotaRelojComun ζ
  have one:=ampliar_paso (paso_constante_igual_a_uno dp) dp (le_max_left 1 _ : 1≤B)
  obtain ⟨src,dest⟩:=pasos_fuente_y_destino dp dy yt zp cut
  have xs:=ampliar_paso src dp ((le_max_left _ _).trans (le_max_right 1 _) :
    normaFuenteDelReloj ζ≤B)
  have xd:=ampliar_paso dest dp ((le_max_right _ _).trans (le_max_right 1 _) :
    normaDestinoDelReloj ζ≤B)
  have per (s b : Bool) : PasoDelReloj (factorTemporal s b y z) (velocidadTemporal s b y z)
      (factorTemporal s b (y-d) (z-d)) d B := by
    cases s <;> cases b
    exacts [one,xd,xs,one]
  let x:=factoresPatron (fun s b => factorTemporal s b y z) t
  let v:=factoresPatron (fun s b => velocidadTemporal s b y z) t
  let w:=factoresPatron (fun s b => factorTemporal s b (y-d) (z-d)) t
  have atoms (i : Fin 4) : PasoDelReloj (x i) (v i) (w i) d B := by
    fin_cases i; exacts [per true _,per true _,per false _,per false _]
  have link:=multiplicar_cuatro_pasos dp x v w (fun _ => B) atoms
  change PasoDelReloj (formaTemporal y z t) (pendienteTemporal y z t) (formaTemporal (y-d) (z-d) t) d
    (27*(B*B*B*B)) at link
  convert link using 1; ring

theorem separacion_espacial_temporal {n} (h : ℕ) (p : FactoresContinuos) (y z : ℝ≥0) (u : Mark n)
    (t : CuatroMarcas) :
    coefDelPerfil h p y z u t=coefDelPerfil h p 1 1 u t*formaTemporal y z t := by
  obtain ⟨o,v,j,l⟩:=t
  cases o <;> cases v <;> cases j <;> cases l <;>
    simp [coefDelPerfil,coefInverso,formaTemporal,monoCuatro,factorTemporal] <;> ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reloj_de_las_dieciseis_marcas
#print axioms ArticuloA.Historias.separacion_espacial_temporal
