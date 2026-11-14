import GeneradorInversoConTasasFisicas
import ErrorDeCadaLineaInversa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def filtrarTasa (U : Prop) (r : ℝ) : ℝ := if U then r else 0

def sumaFuentes {n} (U : Prop) (o : Bool) (e : Cell n) (rate : Vertex→Bool→ℝ) : ℝ :=
  ∑ i : Fin 4,filtrarTasa (U ∧ o=false) (rate (lineLabel e i) true)

def sumaMetas {n} (X : State n) (e f : Cell n) (o v j l : Bool) (rate : Vertex→Bool→ℝ) : ℝ :=
  filtrarTasa (patronInverso X e f o v true l) (rate (lineLabel (corners (e,f)).2 2) j)+
  filtrarTasa (patronInverso X e f o v j true) (rate (lineLabel (corners (e,f)).2 3) l)

def inserciones {n} (X : State n) (e f : Cell n) (o v j l : Bool) (birth : Cell n→ℝ) : ℝ :=
  filtrarTasa (o=true ∧ patronInverso X e f false v j l) (birth e)+
  filtrarTasa (v=true ∧ patronInverso X e f o false j l) (birth f)

def operadorInverso {n} (X : State n) (e f : Cell n) (o v j l : Bool)
    (birth : Cell n→ℝ) (rate : Vertex→Bool→ℝ) : ℝ :=
  let U:=patronInverso X e f o v j l
  inserciones X e f o v j l birth-
    sumaFuentes U o e rate-sumaFuentes U v f rate-sumaMetas X e f o v j l rate

def costoLocal {n} (X : State n) (e f : Cell n) (o v j l : Bool)
    (be : Cell n→ℝ) (re : Vertex→Bool→ℝ) : ℝ :=
  let U:=patronInverso X e f o v j l
  inserciones X e f o v j l be+
    sumaFuentes U o e re+sumaFuentes U v f re+sumaMetas X e f o v j l re

private theorem guarda_resta (P : Prop) (a b : ℝ) :
    filtrarTasa P a-filtrarTasa P b=filtrarTasa P (a-b) := by by_cases h:P <;> simp [filtrarTasa,h]
private theorem abs_guarda (P : Prop) (a : ℝ) : |filtrarTasa P a|=filtrarTasa P |a| := by
  by_cases h:P <;> simp [filtrarTasa,h]
private theorem cota_fuentes {n} (e : Cell n) (U : Prop) (o : Bool) (a b : Vertex→Bool→ℝ) :
    |sumaFuentes U o e a-sumaFuentes U o e b|≤sumaFuentes U o e (fun u j => |a u j-b u j|) := by
  unfold sumaFuentes; rw [←Finset.sum_sub_distrib]
  simpa only [guarda_resta,abs_guarda] using Finset.abs_sum_le_sum_abs
    (fun i : Fin 4 => filtrarTasa (U ∧ o=false) (a (lineLabel e i) true-b (lineLabel e i) true)) Finset.univ

theorem comparar_operadores_inversos {n} (X : State n) (e f : Cell n) (o v j l : Bool)
    (birth birth' : Cell n→ℝ) (a b : Vertex→Bool→ℝ) :
    |operadorInverso X e f o v j l birth a-operadorInverso X e f o v j l birth' b|≤
      costoLocal X e f o v j l (fun e => |birth e-birth' e|) (fun u j => |a u j-b u j|) := by
  have dos (P Q : Prop) (a b c d : ℝ) :
      |(filtrarTasa P a+filtrarTasa Q b)-(filtrarTasa P c+filtrarTasa Q d)| ≤
        filtrarTasa P |a-c|+filtrarTasa Q |b-d| := by
    rw [show (filtrarTasa P a+filtrarTasa Q b)-(filtrarTasa P c+filtrarTasa Q d)=
      (filtrarTasa P a-filtrarTasa P c)+(filtrarTasa Q b-filtrarTasa Q d) by ring]
    simpa only [guarda_resta,abs_guarda] using abs_add_le (filtrarTasa P (a-c)) (filtrarTasa Q (b-d))
  have four (x y z w X Y Z W : ℝ) :
      |(x-y-z-w)-(X-Y-Z-W)|≤|x-X|+|y-Y|+|z-Z|+|w-W| := by
    rw [show (x-y-z-w)-(X-Y-Z-W)=(x-X)-(y-Y)-(z-Z)-(w-W) by ring]
    calc _ ≤ |(x-X)-(y-Y)-(z-Z)|+|w-W| := abs_sub _ _
         _ ≤ (|(x-X)-(y-Y)|+|z-Z|)+|w-W| := by gcongr; exact abs_sub _ _
         _ ≤ _ := by gcongr; exact abs_sub _ _
  exact (four _ _ _ _ _ _ _ _).trans (add_le_add (add_le_add (add_le_add
    (dos _ _ _ _ _ _) (cota_fuentes e _ o a b)) (cota_fuentes f _ v a b)) (dos _ _ _ _ _ _))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.comparar_operadores_inversos
