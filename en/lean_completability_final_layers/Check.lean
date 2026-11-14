import CierreDeLosSeisBloquesDelArticuloA

/-! Prints the statement of the final theorem and the axioms it depends on.
Usage: `lake env lean Check.lean` after `lake build`. -/

#check @ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos
#print axioms ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos
