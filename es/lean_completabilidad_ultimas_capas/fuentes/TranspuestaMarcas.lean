import ExtremosAdjunto
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2

/-- (promoted index, original list, promoted list). -/
abbrev Inc := Fin 4 × List (Fin 4) × List (Fin 4)

def removes {ι} : List ι → List (ι × List ι)
  | [] => []
  | i::J => (i,J)::(removes J).map (fun a => (a.1,i::a.2))

def forwardTerms : List Inc :=
  SizeOn.allMarks.flatMap fun m => ((List.finRange 4).filter (fun i => !(m i))).map
    (fun i => (i,keys m,keys (promote m i)))

def backwardTerms : List Inc :=
  (subsets (List.finRange 4)).flatMap fun J =>
    (removes J).map (fun a => (a.1,a.2,J))

theorem permutation_terms : forwardTerms.Perm backwardTerms := by decide
theorem parity_flip : ∀ e ∈ forwardTerms, parity e.2.1 = !parity e.2.2 := by decide

variable {α ι : Type} (s : ProfileScale α)
theorem permutation_sum (f : ι → α) {xs ys : List ι} (perm : xs.Perm ys) :
    s.sum xs f = s.sum ys f := by
  induction perm with
  | nil => rfl
  | cons i _ ih => exact congrArg (s.add (f i)) ih
  | swap i j L =>
    change s.add _ (s.add _ _) = s.add _ (s.add _ _)
    rw [←s.assoc,s.comm (f j) (f i),s.assoc]
  | trans _ _ ih ij => exact ih.trans ij

theorem pred_sum (f : List ι → α) (p : ι → α) (J : List ι) :
    predecessor s f p J = s.sum (removes J) (fun a => s.mul (p a.1) (f a.2)) := by
  induction J generalizing f with
  | nil => rfl
  | cons i J ih =>
    change s.add _ (predecessor s (fun L => f (i::L)) p J) = s.add _ (s.sum _ _)
    rw [ih,E2.Cart.sum_map]

/-- Transposition for arbitrary weights; the observable may depend on the
promoted pattern, the coefficient on the original pattern, and signs on either. -/
theorem transpose (w : Fin 4 → List (Fin 4) → List (Fin 4) → α) :
    s.sum SizeOn.allMarks (fun m => s.sum ((List.finRange 4).filter (fun i => !(m i)))
      (fun i => w i (keys m) (keys (promote m i)))) =
    s.sum (subsets (List.finRange 4)) (fun J => s.sum (removes J) (fun a => w a.1 a.2 J)) := by
  have eq := permutation_sum s (fun a : Inc => w a.1 a.2.1 a.2.2) permutation_terms
  simpa only [forwardTerms,backwardTerms,E2.Cart.sum_flat,E2.Cart.sum_map] using eq

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.transpose
