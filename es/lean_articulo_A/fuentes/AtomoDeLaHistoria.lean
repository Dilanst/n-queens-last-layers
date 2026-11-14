import DosColoresDelRevelado
import ArbolEtiquetadoDeE2
import CuotasSobreLaPalabra
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n q : ℕ}

def probPaso (x : State n) (u : ColorWeights ℝ≥0) (v : Pieza n) :=
  cuotaElegida x v * ((denominador x u v)⁻¹ * elegido u v)

theorem en_cartesiana (a : Candidata n) : numeros a∈virtualEdges (2*n-1) := by
  unfold virtualEdges
  refine List.mem_flatMap.mpr ⟨_,List.mem_range.mpr (a 0).isLt,List.mem_flatMap.mpr ⟨_,List.mem_range.mpr (a 1).isLt,
    List.mem_flatMap.mpr ⟨_,List.mem_range.mpr (a 2).isLt,List.mem_map.mpr ⟨_,List.mem_range.mpr (a 3).isLt,?_⟩⟩⟩⟩
  funext i; fin_cases i <;> rfl

private theorem seleccion {Y : Type} (l : Atoms ℝ≥0 Y) (fail y : Y) (b : ℝ≥0)
    (nz : total masas l≠0) (mem : (b,y)∈l) :
    ((total masas l)⁻¹*b,y)∈choose masas l fail (·⁻¹) := by
  have nz' : total masas l≠masas.zero := nz
  rw [ProfileKernel.choose,if_neg nz']
  exact List.mem_map.mpr ⟨_,mem,rfl⟩

theorem atomo_de_un_paso (H : Historia n q) (h : ℕ) (lev : q=n-h) (u : ColorWeights ℝ≥0) (t : Indice n)
    (nz : denominador (estado H h t.val) u (secuencia H t)≠0) :
    let x := estado H h t.val
    let v := secuencia H t
    (probPaso x u v,jugada v,estado H h (t.val+1))∈ramas x u := by
  let x := estado H h t.val
  obtain ⟨r,v,live⟩ := cuotas_del_estado H h lev t.val t.isLt.le
  have len : (palabra H).length=2*n-1 := by simp [palabra,lista]
  have col (bs : List Bool) : bs.count true+bs.count false=bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [List.count_cons] at * <;> omega
  have quedan : (estado H h t.val).reals+(estado H h t.val).virtuals≠0 := by
    rw [r,v,col,List.length_drop,len]; have lt:=t.isLt; omega
  change (_,_,estado H h (t.val+1))∈ramas (estado H h t.val) u
  rw [ramas,if_neg (by simp [live]; omega),estado,dif_pos t.isLt]
  apply List.mem_map.mpr
  refine ⟨(probPaso x u (secuencia H t),jugada (secuencia H t)),?_,rfl⟩
  have activo := siguiente_disponible H h t
  cases eq : secuencia H t with
  | real e =>
    rw [eq] at activo nz
    change total masas (realChoices masas x u)≠0 at nz
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨_,seleccion (realChoices masas x u) .fail (.real e) (elegido u (.real e)) nz ?_,rfl⟩
    exact List.mem_map.mpr ⟨e,List.mem_filter.mpr ⟨board_complete e,activo⟩,rfl⟩
  | virtual g =>
    rw [eq] at activo nz
    change total masas (virtualChoices masas x u.virtual)≠0 at nz
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨_,seleccion (virtualChoices masas x u.virtual) .fail (.virtual g) (elegido u (.virtual g)) nz ?_,rfl⟩
    have gg : numeros (tupla H t)=g := congrArg edgeOf eq
    exact List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨gg ▸ en_cartesiana (tupla H t),activo⟩,rfl⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.atomo_de_un_paso
