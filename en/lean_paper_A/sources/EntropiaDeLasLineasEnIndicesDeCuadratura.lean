import SumaDeDosEtiquetadosDeLasMismasFibras
namespace ArticuloA.Historias
open Perfil Repair Trayectoria Trayectoria.E2 Real
open scoped BigOperators
noncomputable section
open Classical

theorem entropia_de_lineas_en_cuadratura (n q : ℕ) (p : FactoresContinuos) :
    entropiaLineas (cargaCelda n q p)=∑ i,∑ j : Indice n,aporteCelda (1-cargaLinea n q p i j) := by
  let a (s : Cell n×Fin 4):=etiquetaDeCasilla s.1 s.2
  let b (s : Cell n×Fin 4):=(s.2,lineaDeCuadratura s.1 s.2)
  let F (i : FibraDeB1 n):=aporteCelda (1-masaBajo (cargaCelda n q p) (enLaFibra i))
  let G (j : Fin 4×Indice n):=aporteCelda (1-cargaLinea n q p j.1 j.2)
  change ∑ i,F i=_
  rw [←Fintype.sum_prod_type (f:=G)]
  apply suma_por_cambio_de_etiquetas a b F G
  · rintro ⟨e,i⟩ ⟨z,j⟩
    exact etiquetas_miden_las_mismas_fibras e z i j
  · rintro ⟨e,i⟩
    obtain ⟨hz,idx⟩:=incidencia_etiquetada e i
    have eq:=carga_sobre_una_fibra_fisica q p _ e hz
    dsimp [a,b,F,G]
    congr 2
    convert eq using 2 <;> simp [idx,lineaDeCuadratura]
  · intro i off
    have empty : ¬∃ z,enLaFibra i z := by
      rintro ⟨z,hz⟩
      apply off
      refine ⟨(z,familiaDeReserva i),?_⟩
      rcases i with ⟨v,j⟩|⟨v,j⟩ <;> cases v <;>
        simpa [a,familiaDeReserva,etiquetaDeCasilla,enLaFibra,etiquetaA,etiquetaD] using hz
    simp [F,masa_nula_de_fibra_vacia _ _ empty,aporteCelda]
  · rintro ⟨i,j⟩ off
    have zero : gradoInicial n p i j=0 := by
      apply Finset.sum_eq_zero
      intro e _
      have ne : lines e i≠j.val:=fun h=>off ⟨(e,i),Prod.ext rfl (Fin.ext h)⟩
      simp [ne]
    simp [G,cargaLinea,zero,aporteCelda]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_de_lineas_en_cuadratura
