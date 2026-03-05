-- -- This is the proof in the style of the Cubical library: Cubical.Foundations.HLevels
-- SqFillSigmaAB' : SqFill (Σ A (λ a → B a))
-- SqFillSigmaAB' l r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
-- SqFillSigmaAB' {lu} {ld} l {ru} {rd} r u d i j .snd =
--     pathToPathP (λ i → PathP (λ j → SqB i j) (u i .snd) (d i .snd)) (cong snd l) (cong snd r)
--     (SqFill→PathPIsProp (λ j → SqB i1 j) (SqFillB (sqA i1 i1)) (snd ru) (snd rd) (transport (λ i → PathP (λ j → SqB i j) (u i .snd) (d i .snd)) (cong snd l)) (cong snd r) )
--     i j
--     where
--     sqA : I → I → A
--     sqA i j = (SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j)

--     SqB : I → I → Type
--     SqB i j = B (sqA i j)

--     -- the key idea is
--     pathToPathP : (A : I → Type) (x : A i0) (y : A i1) → transport (λ i → A i) x ≡ y → PathP A x y
--     pathToPathP A x y p i = hcomp (λ j → λ {
--         (i = i0) → x;
--         (i = i1) → p j
--         }) (transp (λ j → A (i ∧ j)) (~ i) x)


--     -- These modules are Glue-free.
--     open import Cubical.Foundations.Prelude using (ℓ-max; symP; toPathP; hfill; fromPathP)
--     open import Cubical.Foundations.GroupoidLaws using (hcomp-unique)

--     -- The modules below are Gluey. To make it convincing, let's just copy the required definitions.
--     -- open import Cubical.Foundations.Isomorphism using (Iso)
--     -- open import Cubical.Foundations.Path using (PathPIsoPath)
--     -- open import Cubical.Foundations.HLevels using (isPropRetract)
--     module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
--         section : (f : A → B) → (g : B → A) → Type ℓ'
--         section f g = ∀ b → f (g b) ≡ b

--         -- NB: `g` is the retraction!
--         retract : (f : A → B) → (g : B → A) → Type ℓ
--         retract f g = ∀ a → g (f a) ≡ a

--     record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
--         no-eta-equality
--         constructor iso
--         field
--             fun : A → B
--             inv : B → A
--             rightInv : section fun inv
--             leftInv  : retract fun inv

--     PathPIsoPath : ∀ {ℓ} (A : I → Type ℓ) (x : A i0) (y : A i1) → Iso (PathP A x y) (transport (λ i → A i) x ≡ y)
--     PathPIsoPath A x y .Iso.fun = fromPathP
--     PathPIsoPath A x y .Iso.inv = toPathP
--     PathPIsoPath A x y .Iso.rightInv q k i =
--         hcomp
--         (λ j → λ
--             { (i = i0) → slide (j ∨ ~ k)
--             ; (i = i1) → q j
--             ; (k = i0) → transp (λ l → A (i ∨ l)) i (fromPathPFiller j)
--             ; (k = i1) → ∧∨Square i j
--             })
--         (transp (λ l → A (i ∨ ~ k ∨ l)) (i ∨ ~ k)
--             (transp (λ l → (A (i ∨ (~ k ∧ l)))) (k ∨ i)
--             (transp (λ l → A (i ∧ l)) (~ i)
--                 x)))
--         where
--         fromPathPFiller : _
--         fromPathPFiller =
--             hfill
--                 (λ j → λ
--                 { (i = i0) → x
--                 ; (i = i1) → q j })
--                 (inS (transp (λ j → A (i ∧ j)) (~ i) x))

--         slide : I → _
--         slide i = transp (λ l → A (i ∨ l)) i (transp (λ l → A (i ∧ l)) (~ i) x)

--         ∧∨Square : I → I → _
--         ∧∨Square i j =
--             hcomp
--                 (λ l → λ
--                 { (i = i0) → slide j
--                 ; (i = i1) → q (j ∧ l)
--                 ; (j = i0) → slide i
--                 ; (j = i1) → q (i ∧ l)
--                 })
--                 (slide (i ∨ j))
--     PathPIsoPath A x y .Iso.leftInv q k i =
--         outS
--         (hcomp-unique
--             (λ j → λ
--             { (i = i0) → x
--             ; (i = i1) → transp (λ l → A (j ∨ l)) j (q j)
--             })
--             (inS (transp (λ l → A (i ∧ l)) (~ i) x))
--             (λ j → inS (transp (λ l → A (i ∧ (j ∨ l))) (~ i ∨ j) (q (i ∧ j)))))
--         k

--     isPropRetract : ∀ {ℓ} → {A B : Type ℓ} (f : A → B) (g : B → A) (h : (x : A) → g (f x) ≡ x) → isProp B → isProp A
--     isPropRetract f g h p x y i =
--         hcomp
--         (λ j → λ
--             { (i = i0) → h x j
--             ; (i = i1) → h y j})
--         (g (p (f x) (f y) i))

--     -- Kan operations hidden in:
--     -- - isPropRetract has 1 hcomp
--     -- - PathPIsoPath .Iso.leftInv needs uniqueness of hcomp, and also several hcomps
--     SqFill→PathPIsProp : (A : I → Type) (SqFillA : SqFill (A i1)) (x : A i0) (y : A i1) → isProp (PathP A x y)
--     SqFill→PathPIsProp A SqFillA x y = isPropRetract fromPathP (pathToPathP A x y) (PathPIsoPath A x y .Iso.leftInv) (λ p q → SqFillA p q refl refl)
