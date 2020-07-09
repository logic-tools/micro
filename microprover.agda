open import Data.Bool using (Bool; true; false; if_then_else_; T; _∧_; not)
open import Data.Bool.Properties using (T-≡; T-not-≡; T-∧)
open import Data.List using (List; []; _∷_; _++_; [_]; sum; map)
open import Data.List.Properties using (++-identity; ++-assoc; ≡-dec; ++-conicalˡ; ++-conicalʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-++⁻; ∈-map⁺; ∈-++⁺ʳ)
open import Data.List.Membership.DecPropositional as Mem using (_∈?_)
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties as AnyP using (¬Any[])
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; swap; prep; refl)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (All-resp-↭; Any-resp-↭; shift)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _≟_; s≤s; _≡ᵇ_)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function using (id; _on_; _∘_; _$_; const)
open import Function.Equality as Eq using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open Equivalence
import Induction.WellFounded as WF
open import Relation.Binary.PropositionalEquality as PE using (_≡_; refl; sym; cong; inspect)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; True; fromWitness)
open import Relation.Nullary.Implication using (_→-dec_)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Sum using (_⊎-dec_)

------------------------------------------------------------------------
-- Syntax

Id : Set
Id = ℕ

infixr 6 _⇒_

data Form : Set where
  falsity : Form
  pro : (x : Id) → Form
  _⇒_ : (p : Form) (q : Form) → Form

------------------------------------------------------------------------
-- Semantics

Interp : Set _
Interp = Id → Bool

semantics : (i : Interp) (p : Form) → Set
semantics i falsity = ⊥
semantics i (pro x) = T (i x)
semantics i (p ⇒ q) = semantics i p → semantics i q

semantics-ex1 : ∀ {i} → ¬ semantics i falsity
semantics-ex1 ()

semantics-ex2 : ∀ {i p} → semantics i (p ⇒ p)
semantics-ex2 = id

eval : (i : Id → Bool) (p : Form) → Dec (semantics i p)
eval i falsity = no id
eval i (pro x) with i x
... | false = no id
... | true = yes tt
eval i (p ⇒ q) = eval i p →-dec eval i q

semantics' : (i : Interp) (l r : List Form) → Set
semantics' i l r = All (semantics i) l → Any (semantics i) r

------------------------------------------------------------------------
-- Proof System

infix 4 _⟫_

data _⟫_ : (l r : List Form) → Set where
  fls-l : ∀ {l r} → falsity ∷ l ⟫ r
  imp-l : ∀ {p q l r} → l ⟫ p ∷ r → q ∷ l ⟫ r → p ⇒ q ∷ l ⟫ r
  imp-r : ∀ {p q l r} → p ∷ l ⟫ q ∷ r → l ⟫ p ⇒ q ∷ r
  per-l : ∀ {l l' r} → l ⟫ r → l ↭ l' → l' ⟫ r
  per-r : ∀ {l r r'} → l ⟫ r → r ↭ r' → l ⟫ r'
  basic : ∀ {p l r} → p ∷ l ⟫ p ∷ r

-- Soundness

proper-imp-l : ∀ {p q l r} i → (pr : semantics' i l (p ∷ r)) (ql : semantics' i (q ∷ l) r) → semantics' i (p ⇒ q ∷ l) r
proper-imp-l {p} i pr ql lhs with eval i p
proper-imp-l {p} i pr ql (_ All.∷ lhs) | no prf with pr lhs
... | here px = ⊥-elim (prf px)
... | there m = m
proper-imp-l {p} i pr ql (px All.∷ lhs) | yes prf = ql (px prf All.∷ lhs)

proper-imp-r : ∀ {p q l r} i → (plqr : semantics' i (p ∷ l) (q ∷ r)) → semantics' i l (p ⇒ q ∷ r)
proper-imp-r {p} i pqr lhs with eval i p
... | no prf = here (⊥-elim ∘ prf)
... | yes prf with (pqr (prf All.∷ lhs))
... | here is-q = here (const is-q)
... | there in-rest = there in-rest

proper : ∀ {l r} i → l ⟫ r → semantics' i l r
proper i fls-l (() All.∷ _)
proper i (imp-l sc sc') = proper-imp-l i (proper i sc) (proper i sc')
proper i (imp-r sc) = proper-imp-r i (proper i sc)
proper i (per-l sc eq) lhs = proper i sc (All-resp-↭ (↭-sym eq) lhs)
proper i (per-r sc eq) lhs = Any-resp-↭ eq (proper i sc lhs)
proper i basic (px All.∷ _) = here px

-- Weakening

weaken : ∀ {l r} p → l ⟫ r → l ⟫ p ∷ r
weaken p fls-l = fls-l
weaken p (imp-l sc sc') = imp-l (per-r (weaken p sc) (swap p _ refl)) (weaken p sc')
weaken p (imp-r sc) = per-r (imp-r (per-r (weaken p sc) (swap p _ refl))) (swap _ p refl)
weaken p (per-l sc eq) = per-l (weaken p sc) eq
weaken p (per-r sc eq) = per-r (weaken p sc) (prep p eq)
weaken p basic = per-r basic (swap _ p refl)

------------------------------------------------------------------------
-- Termination

-- Recursion pattern

data mpAcc : (a b : List Id) (c d : List Form) → Set where
  mp-fls-l : ∀ a b c → mpAcc a b (falsity ∷ c) []
  mp-fls-r : ∀ a b c d → mpAcc a b c d → mpAcc a b c (falsity ∷ d)
  mp-pro-l : ∀ x a b c → mpAcc (x ∷ a) b c [] → mpAcc a b (pro x ∷ c) []
  mp-pro-r : ∀ x a b c d → mpAcc a (x ∷ b) c d → mpAcc a b c (pro x ∷ d)
  mp-imp-l : ∀ p q a b c → mpAcc a b c [ p ] → mpAcc a b (q ∷ c) [] → mpAcc a b (p ⇒ q ∷ c) []
  mp-imp-r : ∀ p q a b c d → mpAcc a b (p ∷ c) (q ∷ d) → mpAcc a b c (p ⇒ q ∷ d)
  mp-basic : ∀ a b → mpAcc a b [] []

-- Well-foundnedness

size : Form → ℕ
size falsity = 1
size (pro _) = 1
size (p ⇒ q) = 1 + size p + size q

Seq : Set
Seq = List Form × List Form

Args : Set
Args = List Id × List Id × Seq

SeqToℕ : Seq → ℕ
SeqToℕ (l , r) = sum (map size l) + sum (map size r)

ArgsToℕ : Args → ℕ
ArgsToℕ (_ , _ , s) = SeqToℕ s

_<Seq_ : Seq → Seq → Set
_<Seq_ = _<_ on SeqToℕ

_<Args_ : Args → Args → Set
(_ , _ , s) <Args (_ , _ , s') = s <Seq s'

suc+suc : (n m : ℕ) → suc n + m ≤ n + suc m
suc+suc n m rewrite +-suc n m = ≤-refl

mp1 : ∀ {c d} p q → c + (p + 0) ≤ p + q + c + d
mp1 {c} {d} p q rewrite proj₂ +-identity p | +-comm p q | +-assoc q p c | +-comm p c = ≤-stepsʳ d (≤-stepsˡ q ≤-refl)

mp2 : ∀ {c d} p q → q + c + 0 ≤ p + q + c + d
mp2 {c} {d} p q rewrite proj₂ +-identity (q + c) | +-assoc p q c = ≤-stepsʳ d (≤-stepsˡ p ≤-refl)

mp3 : ∀ {c d} p q → suc (p + c + (q + d)) ≤ c + suc (p + q + d)
mp3 {c} {d} p q rewrite +-suc c (p + q + d) | +-comm p c | +-assoc p q d | +-assoc c p (q + d) = s≤s ≤-refl

mk-mpAcc : Args → Set
mk-mpAcc (a , b , c , d) = mpAcc a b c d

mpAccTotal : (x : Args) → mk-mpAcc x
mpAccTotal = wfRec _ _ go
  where
  open WF.InverseImage {A = Args} {_<_ = _<_}  ArgsToℕ using (wellFounded)
  open WF.All (wellFounded <-wellFounded) using (wfRec)
  go : (x : Args) → (∀ y → y <Args x → mk-mpAcc y) → mk-mpAcc x
  go (a , b , falsity ∷ c , []) rec = mp-fls-l a b c
  go (a , b , c , falsity ∷ d) rec = mp-fls-r a b c d
    (rec (a , b , c , d) (suc+suc (sum (map size c)) (sum (map size d))))
  go (a , b , pro x ∷ c , []) rec = mp-pro-l x a b c
    (rec (x ∷ a , b , c , []) (s≤s ≤-refl))
  go (a , b , c , pro x ∷ d) rec = mp-pro-r x a b c d
    (rec (a , x ∷ b , c , d) (suc+suc (sum (map size c)) (sum (map size d))))
  go (a , b , p ⇒ q ∷ c , []) rec = mp-imp-l p q a b c
    (rec (a , b , c , [ p ]) (s≤s (mp1 (size p) (size q))))
    (rec (a , b , q ∷ c , []) (s≤s (mp2 (size p) (size q))))
  go (a , b , c , p ⇒ q ∷ d) rec = mp-imp-r p q a b c d
    (rec (a , b , p ∷ c , q ∷ d) (mp3 (size p) (size q)))
  go (a , b , [] , []) rec = mp-basic a b

------------------------------------------------------------------------
-- Prover that returns counter-examples

Shared : (xs ys : List Id) → Set
Shared xs ys = (Σ Id λ e → e ∈ xs × e ∈ ys)

Shared-contract : ∀ x xs ys → ¬ x ∈ ys → Shared (x ∷ xs) ys → Shared xs ys
Shared-contract x xs ys absent (v , here px , in-ys) rewrite px = ⊥-elim (absent in-ys)
Shared-contract x xs ys absent (v , there in-xs , in-ys) = v , in-xs , in-ys

_id∈?_ : (x : Id) (xs : List Id) → Dec (x ∈ xs)
_id∈?_ x xs = _∈?_ _≟_ x xs

shared : ∀ xs ys → Dec (Shared xs ys)
shared [] ys = no (λ (_ , in-[] , _) → ¬Any[] in-[])
shared (x ∷ xs) ys with x id∈? ys
... | no absent with shared xs ys
... | no disj = no (contraposition (Shared-contract x xs ys absent) disj)
... | yes (v , in-xs , in-ys) = yes (v , there in-xs , in-ys)
shared (x ∷ xs) ys | yes prf = yes (x , here refl , prf)

μ-acc : ∀ {a b c d} → mpAcc a b c d → List (List Id)
μ-acc (mp-fls-l _ _ c) = []
μ-acc (mp-fls-r _ _ _ d s) = μ-acc s
μ-acc (mp-pro-l x _ _ c s) = μ-acc s
μ-acc (mp-pro-r x _ _ _ d s) = μ-acc s
μ-acc (mp-imp-l p q _ _ c s t) = μ-acc s ++ μ-acc t
μ-acc (mp-imp-r p q _ _ _ d s) = μ-acc s
μ-acc (mp-basic a b) = if ⌊ shared a b ⌋ then [] else [ a ]

μ : (a b : List Id) (c d : List Form) → List (List Id)
μ a b c d = μ-acc (mpAccTotal (a , b , c , d))

-- Soundness

shared⟫ : ∀ {l r} p → (lhs : p ∈ l) (rhs : p ∈ r) → l ⟫ r
shared⟫ p lhs rhs with ∈-∃++ lhs | ∈-∃++ rhs
... | l1 , l2 , l-prf | r1 , r2 , r-prf rewrite l-prf | r-prf =
  per-r (per-l basic (↭-sym (shift p l1 l2))) (↭-sym (shift p r1 r2))

proven-acc : ∀ {a b c d} → (s : mpAcc a b c d) (prf : μ-acc s ≡ []) → c ++ map pro a ⟫ d ++ map pro b

proven-acc (mp-fls-l _ _ _) _ = fls-l
proven-acc (mp-fls-r _ _ _ _ s) prf = weaken falsity (proven-acc s prf)
proven-acc (mp-pro-l x a _ c s) prf = per-l (proven-acc s prf) (shift (pro x) c (map pro a))
proven-acc (mp-pro-r x _ b _ d s) prf = per-r (proven-acc s prf) (shift (pro x) d (map pro b))
proven-acc (mp-imp-l _ _ _ _ _ s t) prf = imp-l (proven-acc s (++-conicalˡ _ _ prf)) (proven-acc t (++-conicalʳ _ _ prf))
proven-acc (mp-imp-r _ _ _ _ _ _ s) prf = imp-r (proven-acc s prf)
proven-acc (mp-basic a b) prf with shared a b
... | yes (x , lhs , rhs) = shared⟫ (pro x) (∈-map⁺ pro lhs) (∈-map⁺ pro rhs)

proven : ∀ a b c d → (prf : μ a b c d ≡ []) → c ++ map pro a ⟫ d ++ map pro b
proven a b c d prf = proven-acc (mpAccTotal (a , b , c , d)) prf

sound : ∀ a b c d → (prf : μ a b c d ≡ []) → ∀ i → semantics' i (c ++ map pro a) (d ++ map pro b)
sound a b c d prf i = proper i (proven a b c d prf)

-- Completeness

counter-sem : List Id → Interp
counter-sem a x = ⌊ x id∈? a ⌋

counter-∈ : ∀ x a → T (counter-sem a x) → x ∈ a
counter-∈ x a prf with x id∈? a
... | yes in-there = in-there

counter-common : ∀ a b → ¬ Shared a b → ¬ Any (semantics (counter-sem a)) (map pro b)
counter-common a (x ∷ b) no-shared (here px) = no-shared (x , counter-∈ x a px , here refl)
counter-common a (x ∷ b) no-shared (there prf) =
  counter-common a b (λ (e , in-a , in-b) → no-shared (e , in-a , there in-b)) prf

counter-lhs : ∀ extra a → All (semantics (counter-sem (extra ++ a))) (map pro a)
counter-lhs _ [] = All.[]
counter-lhs extra (x ∷ a) = fromWitness (∈-++⁺ʳ extra (here refl)) All.∷ rec where
  rec : All (semantics (counter-sem (extra ++ [ x ] ++ a))) (map pro a)
  rec rewrite sym (++-assoc extra [ x ] a) = counter-lhs (extra ++ [ x ]) a

Any-update : {A : Set} {P : A → Set} (v v' : A) (xs : List A)
  (prf : Any P (v ∷ xs)) (f : P v → P v') → Any P (v' ∷ xs)
Any-update v v' xs (here pv) f = here (f pv)
Any-update v v' xs (there prf) f = there prf

drop-falsity : ∀ l i → (prf : Any (semantics i) (falsity ∷ l)) → Any (semantics i) l
drop-falsity l i (there prf) = prf

counter-acc : ∀ {a b c d} → (s : mpAcc a b c d) (xs : List Id) (prf : xs ∈ μ-acc s)
  → ¬ semantics' (counter-sem xs) (c ++ map pro a) (d ++ map pro b)
counter-acc (mp-fls-l _ _ c) xs () assm
counter-acc (mp-fls-r _ b _ d s) xs prf assm = counter-acc s xs prf λ lhs →
  drop-falsity (d ++ map pro b) (counter-sem xs) (assm lhs)
counter-acc (mp-pro-l x a _ c s) xs prf assm = counter-acc s xs prf λ lhs →
  assm (All-resp-↭ (shift (pro x) c (map pro a)) lhs)
counter-acc (mp-pro-r x _ b _ d s) xs prf assm = counter-acc s xs prf λ lhs →
  Any-resp-↭ (↭-sym (shift (pro x) d (map pro b))) (assm lhs)
counter-acc (mp-imp-l p q a b c s t) xs prf assm with ∈-++⁻ (μ-acc s) prf | eval (counter-sem xs) p
... | inj₁ in-s | no pf = counter-acc s xs in-s (λ lhs → there (assm ((⊥-elim ∘ pf) All.∷ lhs)))
... | inj₁ in-s | yes pt = counter-acc s xs in-s (const (here pt))
... | inj₂ in-t | _ = counter-acc t xs in-t (λ { (qt All.∷ lhs) → assm ((λ _ → qt) All.∷ lhs) })
counter-acc (mp-imp-r p q a b c d s) xs prf assm = counter-acc s xs prf λ { (pt All.∷ lhs) →
  Any-update (p ⇒ q) q (d ++ map pro b) (assm lhs) (_$ pt) }
counter-acc (mp-basic a b) xs prf assm with shared a b
counter-acc (mp-basic a b) xs (here px) assm | no no-common rewrite px =
  counter-common a b no-common (assm (counter-lhs [] a))

counter : ∀ a b c d xs → (prf : xs ∈ μ a b c d) → ¬ semantics' (counter-sem xs) (c ++ map pro a) (d ++ map pro b)
counter a b c d = counter-acc (mpAccTotal (a , b , c , d))

case-∈ : {A : Set} (xs : List A) → xs ≡ [] ⊎ Σ A (λ x → x ∈ xs)
case-∈ [] = inj₁ refl
case-∈ (x ∷ xs) = inj₂ (x , (here refl))

complete : ∀ a b c d → (valid : ∀ i → semantics' i (c ++ map pro a) (d ++ map pro b)) → μ a b c d ≡ []
complete a b c d valid with case-∈ (μ a b c d)
... | inj₁ prf = prf
... | inj₂ (xs , prf) = ⊥-elim (counter a b c d xs prf (valid (counter-sem xs)))

------------------------------------------------------------------------
-- Micro Prover

member : (v : Id) (xs : List Id) → Bool
member v [] = false
member v (x ∷ xs) = if v ≡ᵇ x then true else member v xs

common : (xs ys : List Id) → Bool
common [] ys = false
common (x ∷ xs) ys = if member x ys then true else common xs ys

mp-acc : ∀ {a b c d} → mpAcc a b c d → Bool
mp-acc (mp-fls-l _ _ c) = true
mp-acc (mp-fls-r _ _ _ d s) = mp-acc s
mp-acc (mp-pro-l x _ _ c s) = mp-acc s
mp-acc (mp-pro-r x _ _ _ d s) = mp-acc s
mp-acc (mp-imp-l p q _ _ c s t) = mp-acc s ∧ mp-acc t
mp-acc (mp-imp-r p q _ _ _ d s) = mp-acc s
mp-acc (mp-basic a b) = common a b

mp : (a b : List Id) (c d : List Form) → Bool
mp a b c d = mp-acc (mpAccTotal (a , b , c , d))

-- Equivalence to μ

ne-≡ᵇ : (v x : Id) (ne : ¬ (v ≡ x)) → (v ≡ᵇ x) ≡ false
ne-≡ᵇ v x ne with v ≡ᵇ x | inspect (v ≡ᵇ_) x
... | false | PE.[ eq ] = refl
... | true | PE.[ eq ] = ⊥-elim (ne (≡ᵇ⇒≡ v x (from T-≡ ⟨$⟩ eq)))

T-if-true-else-x : ∀ b x → T x → T (if b then true else x)
T-if-true-else-x false x prf = prf
T-if-true-else-x true x prf = tt

∈-member : ∀ v xs → v ∈ xs → T (member v xs)
∈-member v .(x ∷ _) (here {x} px) rewrite to T-≡ ⟨$⟩ ≡⇒≡ᵇ v x px = tt
∈-member v .(x ∷ xs) (there {x} {xs} prf) = T-if-true-else-x (v ≡ᵇ x) (member v xs) (∈-member v xs prf)

not-∈-member : ∀ v xs → ¬ v ∈ xs → T (not (member v xs))
not-∈-member v [] prf = tt
not-∈-member v (x ∷ xs) prf with v ≟ x
... | no ne rewrite ne-≡ᵇ v x ne = not-∈-member v xs (prf ∘ there) where
... | yes e = ⊥-elim (prf (here e))

shared-common : (xs ys : List Id) → ⌊ shared xs ys ⌋ ≡ common xs ys
shared-common [] ys = refl
shared-common (x ∷ xs) ys with x id∈? ys
... | no not-there with shared xs ys | inspect (shared xs) ys
... | no prf | PE.[ eq ] rewrite sym (shared-common xs ys) | eq | to T-not-≡ ⟨$⟩ not-∈-member x ys not-there = refl
... | yes prf | PE.[ eq ] rewrite sym (shared-common xs ys) | eq | to T-≡ ⟨$⟩ T-if-true-else-x (member x ys) true tt = refl
shared-common (x ∷ xs) ys | yes in-there rewrite to T-≡ ⟨$⟩ ∈-member x ys in-there = refl

[]-++-[] : {A : Set} {xs ys : List A} (l : xs ≡ []) (r : ys ≡ []) → xs ++ ys ≡ []
[]-++-[] {_} {[]} {[]} l r = refl

μ⇔mp-acc : ∀ {a b c d} → (s : mpAcc a b c d) → μ-acc s ≡ [] ⇔ T (mp-acc s)
μ⇔mp-acc (mp-fls-l _ _ c) = record { to = Eq.const tt ; from = Eq.const refl }
μ⇔mp-acc (mp-fls-r _ _ _ d s) = μ⇔mp-acc s
μ⇔mp-acc (mp-pro-l x _ _ c s) = μ⇔mp-acc s
μ⇔mp-acc (mp-pro-r x _ _ _ d s) = μ⇔mp-acc s
μ⇔mp-acc (mp-imp-l p q _ _ c s t) = record
  { to = record { _⟨$⟩_ = λ empty → from T-∧ ⟨$⟩
         ( to (μ⇔mp-acc s) ⟨$⟩ ++-conicalˡ _ _ empty
         , to (μ⇔mp-acc t) ⟨$⟩ ++-conicalʳ _ _ empty )
         ; cong = cong _ }
  ; from = record { _⟨$⟩_ = λ both → []-++-[]
         (from (μ⇔mp-acc s) ⟨$⟩ proj₁ (to T-∧ ⟨$⟩ both))
         (from (μ⇔mp-acc t) ⟨$⟩ proj₂ (to T-∧ ⟨$⟩ both))
  ; cong = cong _ } }
μ⇔mp-acc (mp-imp-r p q _ _ _ d s) = μ⇔mp-acc s
μ⇔mp-acc (mp-basic a b) with common a b | inspect (common a) b
... | false | PE.[ eq ] rewrite shared-common a b | eq = record
  { to = record { _⟨$⟩_ = λ () ; cong = cong _ } ; from = record { _⟨$⟩_ = λ () ; cong = cong _ } }
... | true | PE.[ eq ] rewrite sym (shared-common a b) | eq =
  record { to = Eq.const tt ; from = Eq.const refl }

μ⇔mp : ∀ a b c d → μ a b c d ≡ [] ⇔ T (mp a b c d)
μ⇔mp a b c d = μ⇔mp-acc (mpAccTotal (a , b , c , d))

------------------------------------------------------------------------
-- Main Result

sound-complete' : ∀ a b c d → (∀ i → semantics' i (c ++ map pro a) (d ++ map pro b)) ⇔ T (mp a b c d)
sound-complete' a b c d = record
  { to = record { _⟨$⟩_ = λ valid → to (μ⇔mp a b c d) ⟨$⟩ complete a b c d valid ; cong = cong _ }
  ; from = record { _⟨$⟩_ = λ sc → sound a b c d (from (μ⇔mp a b c d) ⟨$⟩ sc) ; cong = cong _ } }

prover : Form → Bool
prover p = mp [] [] [] [ p ]

sound-complete : ∀ p → (∀ i → semantics i p) ⇔ T (prover p)
sound-complete p = record
  { to = record { _⟨$⟩_ = λ valid → to (sound-complete' [] [] [] [ p ]) ⟨$⟩ λ i lhs → here (valid i)
                ; cong = cong _ }
  ; from = record { _⟨$⟩_ = λ x i → AnyP.singleton⁻ ((from (sound-complete' [] [] [] [ p ]) ⟨$⟩ x) i All.[])
                  ; cong = cong _ } }

------------------------------------------------------------------------
-- Examples

mp-ex1 : T (prover $ pro 0 ⇒ pro 1 ⇒ pro 0)
mp-ex1 = tt

mp-ex2 : T (prover $ ((pro 0 ⇒ pro 1) ⇒ pro 0) ⇒ pro 0)
mp-ex2 = tt

