{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Test where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r x h y0 =
  eq_rect x h y0

data Unit =
   Tt

data Nat =
   O
 | S Nat

data Prod a b =
   Pair a b

prod_rect :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rect f p =
  case p of {
   Pair x x0 -> f x x0}

data List a =
   Nil
 | Cons a (List a)

data SigT a p =
   ExistT a p

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add m (mul p m)}

type Unconvertible a = Unit

type Crelation a = ()

type Arrow a b = a -> b

type IffT a b = Prod (a -> b) (b -> a)

type Reflexive a r = a -> r

reflexivity :: (Reflexive a1 a2) -> a1 -> a2
reflexivity reflexive =
  reflexive

type Symmetric a r = a -> a -> r -> r

type Transitive a r = a -> a -> a -> r -> r -> r

transitivity :: (Transitive a1 a2) -> a1 -> a1 -> a1 -> a2 -> a2 -> a2
transitivity transitive =
  transitive

data PreOrder a r =
   Build_PreOrder (Reflexive a r) (Transitive a r)

preOrder_Reflexive :: (PreOrder a1 a2) -> Reflexive a1 a2
preOrder_Reflexive preOrder =
  case preOrder of {
   Build_PreOrder preOrder_Reflexive0 _ -> preOrder_Reflexive0}

preOrder_Transitive :: (PreOrder a1 a2) -> Transitive a1 a2
preOrder_Transitive preOrder =
  case preOrder of {
   Build_PreOrder _ preOrder_Transitive0 -> preOrder_Transitive0}

data Equivalence a r =
   Build_Equivalence (Reflexive a r) (Symmetric a r) (Transitive a r)

equivalence_Reflexive :: (Equivalence a1 a2) -> Reflexive a1 a2
equivalence_Reflexive equivalence =
  case equivalence of {
   Build_Equivalence equivalence_Reflexive0 _ _ -> equivalence_Reflexive0}

type Subrelation a r x = a -> a -> r -> x

flip_PreOrder :: (PreOrder a1 a2) -> PreOrder a1 a2
flip_PreOrder h =
  case h of {
   Build_PreOrder preOrder_Reflexive0 preOrder_Transitive0 -> Build_PreOrder preOrder_Reflexive0 (\x y0 z x0 x1 -> preOrder_Transitive0 z y0 x x1 x0)}

type Proper a r = r

type ProperProxy a r = r

reflexive_proper_proxy :: (Reflexive a1 a2) -> a1 -> ProperProxy a1 a2
reflexive_proper_proxy h x =
  h x

type Respectful a b r x = a -> a -> r -> x

subrelation_respectful :: (Subrelation a1 a2 a3) -> (Subrelation a4 a5 a6) -> Subrelation (a1 -> a4) (Respectful a1 a4 a3 a5) (Respectful a1 a4 a2 a6)
subrelation_respectful subl subr x y0 x0 x1 y1 x2 =
  subr (x x1) (y0 y1) (x0 x1 y1 (subl x1 y1 x2))

subrelation_refl :: Subrelation a1 a2 a2
subrelation_refl _ _ x =
  x

subrelation_proper :: a1 -> (Proper a1 a2) -> (Unconvertible (Crelation a1)) -> (Subrelation a1 a2 a3) -> Proper a1 a3
subrelation_proper m mor _ sub =
  sub m m mor

iffT_flip_arrow_subrelation :: (IffT a1 a2) -> Arrow a2 a1
iffT_flip_arrow_subrelation x x0 =
  prod_rect (\_ b -> b x0) x

reflexive_partial_app_morphism :: (a1 -> a2) -> (Proper (a1 -> a2) (Respectful a1 a2 a3 a4)) -> a1 -> (ProperProxy a1 a3) -> Proper a2 a4
reflexive_partial_app_morphism _ h x h0 =
  h x x h0

flip2 :: (Subrelation a1 a2 a3) -> Subrelation a1 a2 a3
flip2 h =
  h

data Prod0 a b =
   Pair0 a b

fst :: (Prod0 a1 a2) -> a1
fst p =
  case p of {
   Pair0 x _ -> x}

snd :: (Prod0 a1 a2) -> a2
snd p =
  case p of {
   Pair0 _ y0 -> y0}

type Subset a = ()

type In a u = u

type Intersection a x0 x = Prod0 x0 x

data Inhabited a u =
   Inhabited_intro a (In a u)

type Included a x0 x = a -> Arrow x0 x

type Same_set a x0 x = a -> IffT x0 x

type RelIncl a b x0 x = a -> Included b x0 x

type Compose s t u f g = SigT t (Prod0 f g)

included_impl :: IffT (a1 -> a2 -> a3) (Included a1 a2 a3)
included_impl =
  Pair (\x -> x) (\x -> x)

same_set_iff :: IffT (a1 -> IffT a2 a3) (Same_set a1 a2 a3)
same_set_iff =
  Pair (\x -> x) (\x -> x)

data Union s t u f =
   Union_intro s (In s u) f

union_eq :: a1 -> Included a2 (Union a1 a2 () a3) a3
union_eq x =
  case included_impl of {
   Pair x0 _ ->
    x0 (\_ x1 ->
      case x1 of {
       Union_intro a _ f0 -> eq_rect x (\f1 -> f1) a f0})}

included_Reflexive :: Included a1 a2 a2
included_Reflexive _ x =
  x

included_Proper :: (Same_set a1 a2 a3) -> (Same_set a1 a4 a5) -> IffT (Included a1 a2 a4) (Included a1 a3 a5)
included_Proper x x0 =
  Pair (\x1 a x2 ->
    let {x3 = x0 a} in prod_rect (\a0 _ -> let {x4 = x1 a} in let {x5 = x a} in prod_rect (\_ b0 -> let {x6 = b0 x2} in let {x7 = x4 x6} in a0 x7) x5) x3)
    (\x1 a x2 -> let {x3 = x0 a} in prod_rect (\_ b -> let {x4 = x1 a} in let {x5 = x a} in prod_rect (\a1 _ -> let {x6 = a1 x2} in let {x7 = x4 x6} in b x7) x5) x3)

same_set_Equivalence :: Equivalence (Subset a1) (Same_set a1 Any Any)
same_set_Equivalence =
  Build_Equivalence (\_ _ -> Pair (\x -> x) (\x -> x)) (\_ _ x a -> Pair (\x0 -> let {x1 = x a} in prod_rect (\_ b -> b x0) x1) (\x0 ->
    let {x1 = x a} in prod_rect (\a0 _ -> a0 x0) x1)) (\_ _ _ x x0 a -> Pair (\x1 ->
    let {x2 = x0 a} in prod_rect (\a0 _ -> let {x3 = x a} in prod_rect (\a1 _ -> let {x4 = a1 x1} in a0 x4) x3) x2) (\x1 ->
    let {x2 = x0 a} in prod_rect (\_ b -> let {x3 = b x1} in let {x4 = x a} in prod_rect (\_ b0 -> b0 x3) x4) x2))

union_compose :: Same_set a3 (Union a2 a3 (Union a1 a2 a4 a5) a6) (Union a1 a3 a4 (Compose a1 a2 a3 a5 a6))
union_compose =
  let {
   x = \_ _ _ ->
    case same_set_iff of {
     Pair x _ -> x}}
  in
  unsafeCoerce x __ __ __ (\_ -> Pair (\x0 ->
    case x0 of {
     Union_intro a i f ->
      case i of {
       Union_intro a0 i0 g -> Union_intro a0 i0 (ExistT a (Pair0 g f))}}) (\x0 ->
    case x0 of {
     Union_intro a i c ->
      case c of {
       ExistT x1 p ->
        case p of {
         Pair0 g f -> Union_intro x1 (Union_intro a i g) f}}}))

union_monotone :: (RelIncl a1 a2 a4 a5) -> Included a2 (Union a1 a2 a3 a4) (Union a1 a2 a3 a5)
union_monotone x =
  case included_impl of {
   Pair x0 _ ->
    x0 (\x1 x2 ->
      case x2 of {
       Union_intro a i f -> Union_intro a i (x a x1 f)})}

type Prod_op a b fA fB = Prod0 fA fB

data T a le =
   Build_t (a -> le) (a -> a -> a -> le -> le -> le)

le_refl :: (T a1 a2) -> a1 -> a2
le_refl t =
  case t of {
   Build_t le_refl0 _ -> le_refl0}

le_trans :: (T a1 a2) -> a1 -> a1 -> a1 -> a2 -> a2 -> a2
le_trans t =
  case t of {
   Build_t _ le_trans0 -> le_trans0}

preOrder_I :: (T a1 a2) -> PreOrder a1 a2
preOrder_I tle =
  Build_PreOrder (le_refl tle) (le_trans tle)

discrete :: T a1 ()
discrete =
  Build_t __ __

product :: (T a1 a2) -> (T a3 a4) -> T (Prod0 a1 a3) (Prod_op a1 a3 a2 a4)
product tA tB =
  Build_t (\x -> Pair0 (le_refl tA (fst x)) (le_refl tB (snd x))) (\x y0 z h h0 ->
    case x of {
     Pair0 a b ->
      case y0 of {
       Pair0 a0 b0 ->
        case z of {
         Pair0 a1 b1 ->
          case h of {
           Pair0 l l0 ->
            case h0 of {
             Pair0 l1 l2 -> Pair0 (transitivity (preOrder_Transitive (preOrder_I tA)) a a0 a1 l l1)
              (transitivity (preOrder_Transitive (preOrder_I tB)) b b0 b1 l0 l2)}}}}})

data T0 a le eq =
   Build_t0 (T a le) (a -> a -> eq -> a -> a -> eq -> IffT le le) (a -> a -> le -> le -> eq)

preO :: (T0 a1 a2 a3) -> T a1 a2
preO t =
  case t of {
   Build_t0 preO0 _ _ -> preO0}

discrete0 :: T0 a1 () ()
discrete0 =
  Build_t0 discrete __ __

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

data PreOrder0 =
   Build_PreOrder0

type PO_car = Any

type Le = Any

type Down = Prod Le Le

type Downset u = Union PO_car PO_car u Le

type T1 =
  PreOrder0
  -- singleton inductive, whose constructor was Build_t
  
type Cov x = Any

data T2 =
   Build_t1 (PO_car -> () -> (In PO_car Any) -> Cov Any) (PO_car -> () -> (Cov Any) -> () -> (PO_car -> (In PO_car Any) -> Cov Any) -> Cov Any) (PO_car -> PO_car ->
                                                                                                                                                () -> Le -> (Cov 
                                                                                                                                                Any) -> Cov Any) 
 (PO_car -> () -> () -> (Cov Any) -> (Cov Any) -> Cov (Intersection PO_car (Downset Any) (Downset Any)))

refl :: T1 -> T2 -> PO_car -> (In PO_car a1) -> Cov a1
refl _ t a x =
  case t of {
   Build_t1 refl0 _ _ _ -> unsafeCoerce refl0 a __ x}

trans :: T1 -> T2 -> PO_car -> (Cov a1) -> (PO_car -> (In PO_car a1) -> Cov a2) -> Cov a2
trans _ t a x x0 =
  case t of {
   Build_t1 _ trans0 _ _ -> unsafeCoerce trans0 a __ x __ x0}

le_left :: T1 -> T2 -> PO_car -> PO_car -> Le -> (Cov a1) -> Cov a1
le_left _ t a b x x0 =
  case t of {
   Build_t1 _ _ le_left2 _ -> le_left2 a b __ x x0}

le_right :: T1 -> T2 -> PO_car -> (Cov a1) -> (Cov a2) -> Cov (Intersection PO_car (Downset a1) (Downset a2))
le_right _ t a x x0 =
  case t of {
   Build_t1 _ _ _ le_right1 -> le_right1 a __ __ x x0}

monotone :: T1 -> T2 -> (Included PO_car a1 a2) -> PO_car -> (Cov a1) -> Cov a2
monotone a fTS uV a0 covaU =
  trans a fTS a0 covaU (\a1 x -> refl a fTS a1 (uV a1 x))

cov_Proper :: T1 -> T2 -> PO_car -> PO_car -> Le -> (Included PO_car a1 a2) -> Arrow (Cov a1) (Cov a2)
cov_Proper a fTS x y0 x0 x1 x2 =
  le_left a fTS y0 x x0 (monotone a fTS x1 x x2)

type T3 =
  PreOrder0
  -- singleton inductive, whose constructor was Build_t
  
s :: T3 -> PreOrder0
s t =
  t

type Ix = Any

type C = Any

data GCov u =
   Grefl u
 | Gle_left PO_car Le (GCov u)
 | Ginfinity Ix (PO_car -> C -> GCov u)

gCov_rect :: T3 -> (PO_car -> () -> Any -> a1) -> (PO_car -> () -> PO_car -> Le -> (GCov Any) -> a1 -> a1) -> (PO_car -> () -> Ix -> (PO_car -> C -> GCov Any) ->
             (PO_car -> C -> a1) -> a1) -> PO_car -> (GCov a2) -> a1
gCov_rect a f f0 f1 a0 g =
  case g of {
   Grefl y0 -> unsafeCoerce f a0 __ y0;
   Gle_left b l g0 -> unsafeCoerce f0 a0 __ b l g0 (gCov_rect a f f0 f1 b g0);
   Ginfinity i g0 -> unsafeCoerce f1 a0 __ i g0 (\u c -> gCov_rect a f f0 f1 u (g0 u c))}

gmonotone :: T3 -> PO_car -> (Included PO_car a1 a2) -> (GCov a1) -> GCov a2
gmonotone a a0 uV aU =
  gCov_rect a (\a1 _ u uV0 -> Grefl (unsafeCoerce uV0 a1 u)) (\_ _ b l _ iHaU uV0 -> Gle_left b l (iHaU uV0)) (\_ _ i _ x uV0 -> Ginfinity i (\u x0 -> x u x0 uV0))
    a0 aU uV

gsubset_equiv :: T3 -> (Same_set PO_car a1 a2) -> PO_car -> IffT (GCov a1) (GCov a2)
gsubset_equiv a uV a0 =
  Pair
    (gmonotone a a0
      (subrelation_proper __ (unsafeCoerce (\_ _ x _ _ -> included_Proper x)) Tt
        (subrelation_respectful subrelation_refl (subrelation_respectful subrelation_refl (flip2 (\_ _ -> iffT_flip_arrow_subrelation)))) __ __ uV __ __
        (reflexive_proper_proxy (equivalence_Reflexive same_set_Equivalence) __) (reflexivity (\_ -> included_Reflexive) __)))
    (gmonotone a a0
      (reflexive_partial_app_morphism __
        (subrelation_proper __ (unsafeCoerce (\_ _ x _ _ -> included_Proper x)) Tt
          (subrelation_respectful subrelation_refl (subrelation_respectful subrelation_refl (flip2 (\_ _ -> iffT_flip_arrow_subrelation))))) __
        (reflexive_proper_proxy (equivalence_Reflexive same_set_Equivalence) __) __ __ uV (reflexivity (\_ -> included_Reflexive) __)))

data GtPos =
   Build_gtPos (PO_car -> PO_car -> Le -> Any -> Any) (PO_car -> Ix -> Any -> Inhabited PO_car (Intersection PO_car C Any)) (PO_car -> () -> (Any -> GCov Any) ->
                                                                                                                            GCov Any)

type GPos = Any

gmono_le :: T3 -> GtPos -> PO_car -> PO_car -> Le -> GPos -> GPos
gmono_le _ gtPos =
  case gtPos of {
   Build_gtPos gmono_le0 _ _ -> gmono_le0}

gmono_ax :: T3 -> GtPos -> PO_car -> Ix -> GPos -> Inhabited PO_car (Intersection PO_car C GPos)
gmono_ax _ gtPos =
  case gtPos of {
   Build_gtPos _ gmono_ax0 _ -> gmono_ax0}

gpositive :: T3 -> GtPos -> PO_car -> (GPos -> GCov a1) -> GCov a1
gpositive _ gtPos a x =
  case gtPos of {
   Build_gtPos _ _ gpositive0 -> unsafeCoerce gpositive0 a __ x}

toPreSpace :: T3 -> T1
toPreSpace a =
  s a

gall_Pos :: T3 -> (PO_car -> Ix -> Inhabited PO_car C) -> GtPos
gall_Pos _ h =
  Build_gtPos __ (\a i _ ->
    let {i0 = h a i} in
    case i0 of {
     Inhabited_intro x p -> Inhabited_intro x (Pair0 p __)}) (\_ _ x -> x __)

type Localized = PO_car -> PO_car -> Le -> Ix -> SigT Ix (PO_car -> C -> SigT PO_car (Prod C Down))

gCov_stable :: T3 -> (T PO_car Le) -> Localized -> PO_car -> PO_car -> (Cov Any) -> (Cov Any) -> PO_car -> Le -> Le -> Cov
               (Intersection PO_car (Downset Any) (Downset Any))
gCov_stable a pO1 loc1 a0 b aU bV =
  gCov_rect a (\a1 _ u ->
    gCov_rect a (\a2 _ u0 _ x x0 -> unsafeCoerce (Grefl (Pair0 (Union_intro a1 u x) (Union_intro a2 u0 x0)))) (\a2 _ b0 l _ iHbV c x x0 ->
      iHbV c x (transitivity (preOrder_Transitive (preOrder_I pO1)) c a2 b0 x0 l)) (\a2 _ i _ x c x0 x1 ->
      let {loc2 = loc1 c a2 x1 i} in
      case loc2 of {
       ExistT j loc' ->
        unsafeCoerce (Ginfinity j (\u0 x2 ->
          let {loc'0 = loc' u0 x2} in
          case loc'0 of {
           ExistT x3 p ->
            case p of {
             Pair c0 d ->
              case d of {
               Pair l l0 -> unsafeCoerce x x3 c0 u0 (transitivity (preOrder_Transitive (preOrder_I pO1)) u0 c a1 l x0) l0}}}))}) b (unsafeCoerce bV))
    (\a1 _ b0 l _ iHaU c ca cb -> iHaU c (transitivity (preOrder_Transitive (preOrder_I pO1)) c a1 b0 ca l) cb) (\a1 _ i _ x c ca cb ->
    let {loc2 = loc1 c a1 ca i} in
    case loc2 of {
     ExistT j loc' ->
      unsafeCoerce (Ginfinity j (\u x0 ->
        let {loc'0 = loc' u x0} in
        case loc'0 of {
         ExistT x1 p ->
          case p of {
           Pair c0 d ->
            case d of {
             Pair l l0 -> unsafeCoerce x x1 c0 u l0 (transitivity (preOrder_Transitive (preOrder_I pO1)) u c b l cb)}}}))}) a0 (unsafeCoerce aU)

gCov_formtop :: T3 -> (T PO_car Le) -> Localized -> T2
gCov_formtop a pO1 loc1 =
  Build_t1 (unsafeCoerce (\_ _ x -> Grefl x)) (\a0 _ aU _ h ->
    gCov_rect a (\a1 _ u h0 -> h0 a1 u) (\_ _ b l _ iHaU h0 -> unsafeCoerce (Gle_left b l (unsafeCoerce iHaU h0))) (\_ _ i _ x h0 ->
      unsafeCoerce (Ginfinity i (\u x0 -> unsafeCoerce x u x0 h0))) a0 (unsafeCoerce aU) h) (\_ b _ x x0 -> unsafeCoerce (Gle_left b x (unsafeCoerce x0)))
    (\a0 _ _ x x0 ->
    gCov_stable a pO1 loc1 a0 a0 x x0 a0 (reflexivity (preOrder_Reflexive (preOrder_I pO1)) a0) (reflexivity (preOrder_Reflexive (preOrder_I pO1)) a0))

data T4 f_ =
   Build_t2 (PO_car -> Cov (Union PO_car PO_car () f_)) (PO_car -> PO_car -> PO_car -> Le -> f_ -> f_) (PO_car -> PO_car -> PO_car -> f_ -> f_ -> Cov
                                                                                                       (Union PO_car PO_car Down f_)) (PO_car -> PO_car -> () -> f_
                                                                                                                                      -> (Cov Any) -> Cov
                                                                                                                                      (Union PO_car PO_car Any f_))

here :: T1 -> T1 -> (T4 a1) -> PO_car -> Cov (Union PO_car PO_car () a1)
here _ _ t =
  case t of {
   Build_t2 here1 _ _ _ -> here1}

le_left0 :: T1 -> T1 -> (T4 a1) -> PO_car -> PO_car -> PO_car -> Le -> a1 -> a1
le_left0 _ _ t =
  case t of {
   Build_t2 _ le_left2 _ _ -> le_left2}

local :: T1 -> T1 -> (T4 a1) -> PO_car -> PO_car -> PO_car -> a1 -> a1 -> Cov (Union PO_car PO_car Down a1)
local _ _ t =
  case t of {
   Build_t2 _ _ local2 _ -> local2}

cov :: T1 -> T1 -> (T4 a1) -> PO_car -> PO_car -> a1 -> (Cov a2) -> Cov (Union PO_car PO_car a2 a1)
cov _ _ t a b x x0 =
  case t of {
   Build_t2 _ _ _ cov0 -> cov0 a b __ x x0}

type Sat f_ = Cov f_

data Pt f =
   Build_pt (Inhabited PO_car f) (PO_car -> PO_car -> f -> f -> Inhabited PO_car (Intersection PO_car Down f)) (PO_car -> () -> f -> (Cov Any) -> Inhabited PO_car
                                                                                                               (Intersection PO_car f Any))

pt_here :: T1 -> (Pt a1) -> Inhabited PO_car a1
pt_here _ p =
  case p of {
   Build_pt pt_here0 _ _ -> pt_here0}

pt_local :: T1 -> (Pt a1) -> PO_car -> PO_car -> a1 -> a1 -> Inhabited PO_car (Intersection PO_car Down a1)
pt_local _ p =
  case p of {
   Build_pt _ pt_local0 _ -> pt_local0}

pt_cov :: T1 -> (Pt a1) -> PO_car -> a1 -> (Cov a2) -> Inhabited PO_car (Intersection PO_car a1 a2)
pt_cov _ p b x x0 =
  case p of {
   Build_pt _ _ pt_cov0 -> unsafeCoerce pt_cov0 b __ x x0}

sat_mono2 :: T1 -> T1 -> T2 -> RelIncl PO_car PO_car a1 (Sat a1)
sat_mono2 s1 _ fTS _ a0 x =
  refl s1 fTS a0 x

type Id = Le

t_id :: T1 -> (T PO_car Le) -> T2 -> T4 Id
t_id s1 pOS fTS =
  Build_t2 (\a -> refl s1 fTS a (Union_intro a __ (reflexivity (preOrder_Reflexive (preOrder_I pOS)) a))) (\a b c x x0 -> le_trans pOS a c b x x0) (\a _ _ x x0 ->
    refl s1 fTS a (Union_intro a (Pair x x0) (reflexivity (preOrder_Reflexive (preOrder_I pOS)) a))) (\a b _ x x0 ->
    le_left s1 fTS a b x (trans s1 fTS b x0 (\b0 x1 -> refl s1 fTS b0 (Union_intro b0 x1 (reflexivity (preOrder_Reflexive (preOrder_I pOS)) b0)))))

t_compose :: T1 -> T2 -> T1 -> T1 -> (T4 a1) -> (T4 a2) -> T4 (Compose PO_car PO_car PO_car a2 a1)
t_compose s1 fTS t u x x0 =
  Build_t2 (\a ->
    let {x1 = here s1 t x a} in
    trans s1 fTS a x1 (\a0 x2 ->
      case x2 of {
       Union_intro a1 _ f ->
        let {x3 = here t u x0 a1} in
        let {x4 = cov s1 t x a0 a1 f x3} in
        monotone s1 fTS
          (subrelation_proper __ (unsafeCoerce (\_ _ x5 _ _ -> included_Proper x5)) Tt
            (subrelation_respectful subrelation_refl (subrelation_respectful subrelation_refl (flip2 (\_ _ -> iffT_flip_arrow_subrelation)))) __ __ union_compose __
            __ (reflexive_proper_proxy (equivalence_Reflexive same_set_Equivalence) __) (reflexivity (\_ -> included_Reflexive) __)) a0 x4})) (\a _ c x1 x2 ->
    case x2 of {
     ExistT t1 p ->
      case p of {
       Pair0 fat1 gt1b -> ExistT t1 (Pair0 fat1 (le_left0 s1 t x a t1 c x1 gt1b))}}) (\a b c x1 x2 ->
    case x1 of {
     ExistT t1 p ->
      case p of {
       Pair0 gt1b fat1 ->
        case x2 of {
         ExistT t2 p0 ->
          case p0 of {
           Pair0 gt2b fat2 ->
            let {x3 = local s1 t x a t1 t2 fat1 fat2} in
            trans s1 fTS a x3 (\a0 x4 ->
              case x4 of {
               Union_intro tt0 i x5 ->
                case i of {
                 Pair downtt fatt ->
                  monotone s1 fTS
                    (subrelation_proper __ (unsafeCoerce (\_ _ x6 _ _ -> included_Proper x6)) Tt
                      (subrelation_respectful subrelation_refl (subrelation_respectful subrelation_refl (flip2 (\_ _ -> iffT_flip_arrow_subrelation)))) __ __
                      union_compose __ __ (reflexive_proper_proxy (equivalence_Reflexive same_set_Equivalence) __) (reflexivity (\_ -> included_Reflexive) __)) a0
                    (cov s1 t x a0 tt0 x5 (local t u x0 tt0 b c (le_left0 t u x0 tt0 b t1 downtt gt1b) (le_left0 t u x0 tt0 c t2 fatt gt2b)))}})}}}})
    (\a b _ x1 x2 ->
    case x1 of {
     ExistT t0 p ->
      case p of {
       Pair0 gtb fat ->
        monotone s1 fTS
          (subrelation_proper __ (unsafeCoerce (\_ _ x3 _ _ -> included_Proper x3)) Tt
            (subrelation_respectful subrelation_refl (subrelation_respectful subrelation_refl (flip2 (\_ _ -> iffT_flip_arrow_subrelation)))) __ __ union_compose __
            __ (reflexive_proper_proxy (equivalence_Reflexive same_set_Equivalence) __) (reflexivity (\_ -> included_Reflexive) __)) a
          (cov s1 t x a t0 fat (cov t u x0 t0 b gtb x2))}})

data T5 f_ =
   Build_t3 (PO_car -> Cov (Union PO_car PO_car () f_)) (PO_car -> PO_car -> PO_car -> f_ -> f_ -> Cov (Union PO_car PO_car Down f_)) (PO_car -> PO_car -> PO_car ->
                                                                                                                                      Le -> f_ -> f_) (PO_car ->
                                                                                                                                                      PO_car ->
                                                                                                                                                      PO_car -> f_ ->
                                                                                                                                                      Le -> f_) 
 (PO_car -> PO_car -> Ix -> f_ -> Cov (Union PO_car PO_car C f_))

here0 :: T1 -> T3 -> (T5 a1) -> PO_car -> Cov (Union PO_car PO_car () a1)
here0 _ _ t =
  case t of {
   Build_t3 here1 _ _ _ _ -> here1}

local0 :: T1 -> T3 -> (T5 a1) -> PO_car -> PO_car -> PO_car -> a1 -> a1 -> Cov (Union PO_car PO_car Down a1)
local0 _ _ t =
  case t of {
   Build_t3 _ local2 _ _ _ -> local2}

le_left1 :: T1 -> T3 -> (T5 a1) -> PO_car -> PO_car -> PO_car -> Le -> a1 -> a1
le_left1 _ _ t =
  case t of {
   Build_t3 _ _ le_left2 _ _ -> le_left2}

le_right0 :: T1 -> T3 -> (T5 a1) -> PO_car -> PO_car -> PO_car -> a1 -> Le -> a1
le_right0 _ _ t =
  case t of {
   Build_t3 _ _ _ le_right1 _ -> le_right1}

ax_right :: T1 -> T3 -> (T5 a1) -> PO_car -> PO_car -> Ix -> a1 -> Cov (Union PO_car PO_car C a1)
ax_right _ _ t =
  case t of {
   Build_t3 _ _ _ _ ax_right0 -> ax_right0}

cont :: T1 -> T3 -> T2 -> (T5 a1) -> T4 a1
cont s1 t fTS x =
  Build_t2 (\a -> here0 s1 t x a) (\a b c x0 x1 -> le_left1 s1 t x a b c x0 x1) (\a b c x0 x1 -> local0 s1 t x a b c x0 x1) (\a b _ x0 x1 ->
    gCov_rect t (\a0 _ u a1 x2 -> refl s1 fTS a1 (Union_intro a0 u x2)) (\a0 _ b0 l _ iHX1 a1 x2 -> iHX1 a1 (le_right0 s1 t x a1 a0 b0 x2 l)) (\a0 _ i _ x2 a1 x3 ->
      let {x4 = ax_right s1 t x a1 a0 i x3} in
      trans s1 fTS a1 x4 (\a2 x5 ->
        case x5 of {
         Union_intro a3 i0 f -> x2 a3 i0 a2 f})) b (unsafeCoerce x1) a x0)

cov_Sat :: T1 -> T3 -> (T PO_car Le) -> T2 -> PO_car -> (Cov (Union PO_car PO_car a1 a2)) -> Cov (Union PO_car PO_car a1 (Sat a2))
cov_Sat s1 t pOS fTS a x =
  cov_Proper s1 fTS a a (reflexivity (preOrder_Reflexive (flip_PreOrder (preOrder_I pOS))) a) (union_monotone (sat_mono2 s1 (toPreSpace t) fTS)) x

converse :: T1 -> T3 -> (T PO_car Le) -> T2 -> (T4 a1) -> T5 (Sat a1)
converse s1 t pOS fTS x =
  Build_t3 (\a -> cov_Sat s1 t pOS fTS a (here s1 (toPreSpace t) x a)) (\a b c x0 x1 ->
    cov_Sat s1 t pOS fTS a
      (let {x2 = le_right s1 fTS a x0 x1} in
       trans s1 fTS a x2 (\a0 x3 ->
         case x3 of {
          Pair0 d d0 ->
           case d of {
            Union_intro a1 i l ->
             case d0 of {
              Union_intro a2 i0 l0 -> local s1 (toPreSpace t) x a0 b c (le_left0 s1 (toPreSpace t) x a0 b a1 l i) (le_left0 s1 (toPreSpace t) x a0 c a2 l0 i0)}}})))
    (\a _ c x0 x1 -> le_left s1 fTS a c x0 x1) (\a b c x0 x1 ->
    trans s1 fTS a x0 (\a0 x2 ->
      let {x3 = Gle_left c x1 (Grefl __)} in let {x4 = cov s1 (toPreSpace t) x a0 b} in monotone s1 fTS (union_eq c) a0 (unsafeCoerce x4 x2 x3))) (\a b j x0 ->
    trans s1 fTS a x0 (\a0 x1 -> cov_Sat s1 t pOS fTS a0 (cov s1 (toPreSpace t) x a0 b x1 (unsafeCoerce (Ginfinity j (\_ x2 -> Grefl x2))))))

data IGT =
   Build_IGT T3 (T PO_car Le) Localized GtPos

s0 :: IGT -> T3
s0 i =
  case i of {
   Build_IGT s1 _ _ _ -> s1}

pO :: IGT -> T PO_car Le
pO i =
  case i of {
   Build_IGT _ pO1 _ _ -> pO1}

localized :: IGT -> Localized
localized i =
  case i of {
   Build_IGT _ _ localized0 _ -> localized0}

pos :: IGT -> GtPos
pos i =
  case i of {
   Build_IGT _ _ _ pos2 -> pos2}

iGT_PreO :: IGT -> T PO_car Le
iGT_PreO x =
  pO x

local1 :: IGT -> Localized
local1 x =
  localized x

iGTFT :: IGT -> T2
iGTFT x =
  gCov_formtop (s0 x) (iGT_PreO x) (local1 x)

iGT_Pos :: IGT -> GtPos
iGT_Pos x =
  pos x

type Cmap =
  T4 Any
  -- singleton inductive, whose constructor was Build_cmap
  
type Mp = Any

mp_ok :: IGT -> IGT -> Cmap -> T4 Mp
mp_ok _ _ c =
  c

id :: IGT -> Cmap
id lA =
  t_id (toPreSpace (s0 lA)) (iGT_PreO lA) (iGTFT lA)

comp :: IGT -> IGT -> IGT -> Cmap -> Cmap -> Cmap
comp lA lB lD f g =
  unsafeCoerce t_compose (toPreSpace (s0 lA)) (iGTFT lA) (toPreSpace (s0 lB)) (toPreSpace (s0 lD)) (mp_ok lA lB g) (mp_ok lB lD f)

data Setoid =
   Build_Setoid

type Sty = Any

unit_Setoid :: Setoid
unit_Setoid =
  Build_Setoid

prod_Setoid :: Setoid -> Setoid -> Setoid
prod_Setoid _ _ =
  Build_Setoid

data Iso =
   Build_Iso (Sty -> Sty) (Sty -> Sty)

to :: Setoid -> Setoid -> Iso -> Sty -> Sty
to _ _ i =
  case i of {
   Build_Iso to1 _ -> to1}

from :: Setoid -> Setoid -> Iso -> Sty -> Sty
from _ _ i =
  case i of {
   Build_Iso _ from1 -> from1}

iso_Sym :: Setoid -> Setoid -> Iso -> Iso
iso_Sym a b i =
  Build_Iso (from a b i) (to a b i)

iso_Trans :: Setoid -> Setoid -> Setoid -> Iso -> Iso -> Iso
iso_Trans a b c ab bc =
  Build_Iso (\x -> to b c bc (to a b ab x)) (\x -> from a b ab (from b c bc x))

type CCat u =
  u -> u -> u
  -- singleton inductive, whose constructor was Build_CCat
  
type Arrow0 u = Any

prod :: (CCat a1) -> a1 -> a1 -> a1
prod cCat =
  cCat

data CMC u =
   Build_CMC (u -> Arrow0 u) (u -> u -> u -> (Arrow0 u) -> (Arrow0 u) -> Arrow0 u) u (u -> Arrow0 u) (u -> u -> Arrow0 u) (u -> u -> Arrow0 u) (u -> u -> u ->
                                                                                                                                               (Arrow0 u) -> (Arrow0
                                                                                                                                               u) -> Arrow0 u)

id0 :: (CCat a1) -> (CMC a1) -> a1 -> Arrow0 a1
id0 _ cMC =
  case cMC of {
   Build_CMC id1 _ _ _ _ _ _ -> id1}

compose :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> (Arrow0 a1) -> (Arrow0 a1) -> Arrow0 a1
compose _ cMC =
  case cMC of {
   Build_CMC _ compose0 _ _ _ _ _ -> compose0}

unit0 :: (CCat a1) -> (CMC a1) -> a1
unit0 _ cMC =
  case cMC of {
   Build_CMC _ _ unit1 _ _ _ _ -> unit1}

tt :: (CCat a1) -> (CMC a1) -> a1 -> Arrow0 a1
tt _ cMC =
  case cMC of {
   Build_CMC _ _ _ tt0 _ _ _ -> tt0}

fst0 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Arrow0 a1
fst0 _ cMC =
  case cMC of {
   Build_CMC _ _ _ _ fst1 _ _ -> fst1}

snd0 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Arrow0 a1
snd0 _ cMC =
  case cMC of {
   Build_CMC _ _ _ _ _ snd1 _ -> snd1}

pair :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> (Arrow0 a1) -> (Arrow0 a1) -> Arrow0 a1
pair _ cMC =
  case cMC of {
   Build_CMC _ _ _ _ _ _ pair1 -> pair1}

parallel :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> a1 -> (Arrow0 a1) -> (Arrow0 a1) -> Arrow0 a1
parallel ccat h a b c d f g =
  pair ccat h (prod ccat a c) b d (compose ccat h (prod ccat a c) a b f (fst0 ccat h a c)) (compose ccat h (prod ccat a c) c d g (snd0 ccat h a c))

data Iso0 u =
   Build_Iso0 (Arrow0 u) (Arrow0 u)

to0 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (Iso0 a1) -> Arrow0 a1
to0 _ _ _ _ i =
  case i of {
   Build_Iso0 to1 _ -> to1}

from0 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (Iso0 a1) -> Arrow0 a1
from0 _ _ _ _ i =
  case i of {
   Build_Iso0 _ from1 -> from1}

ap0 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (Arrow0 a1) -> Arrow0 a1
ap0 ccat h __U0393_ a f =
  compose ccat h __U0393_ (unit0 ccat h) a f (tt ccat h __U0393_)

ap2 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> a1 -> (Arrow0 a1) -> (Arrow0 a1) -> (Arrow0 a1) -> Arrow0 a1
ap2 ccat h __U0393_ a b c f x y0 =
  compose ccat h __U0393_ (prod ccat a b) c f (pair ccat h __U0393_ a b x y0)

add_unit_left :: (CCat a1) -> (CMC a1) -> a1 -> Arrow0 a1
add_unit_left ccat h a =
  pair ccat h a (unit0 ccat h) a (tt ccat h a) (id0 ccat h a)

iso_Refl :: (CCat a1) -> (CMC a1) -> a1 -> Iso0 a1
iso_Refl ccat cmc a =
  Build_Iso0 (id0 ccat cmc a) (id0 ccat cmc a)

iso_Sym0 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (Iso0 a1) -> Iso0 a1
iso_Sym0 ccat cmc a b i =
  Build_Iso0 (from0 ccat cmc a b i) (to0 ccat cmc a b i)

iso_Trans0 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> (Iso0 a1) -> (Iso0 a1) -> Iso0 a1
iso_Trans0 ccat cmc a b c ab bc =
  Build_Iso0 (compose ccat cmc a b c (to0 ccat cmc b c bc) (to0 ccat cmc a b ab)) (compose ccat cmc c b a (from0 ccat cmc a b ab) (from0 ccat cmc b c bc))

iso_Prod :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> a1 -> (Iso0 a1) -> (Iso0 a1) -> Iso0 a1
iso_Prod ccat cmc a b a' b' a0 b0 =
  Build_Iso0 (parallel ccat cmc a a' b b' (to0 ccat cmc a a' a0) (to0 ccat cmc b b' b0))
    (parallel ccat cmc a' a b' b (from0 ccat cmc a a' a0) (from0 ccat cmc b b' b0))

prod_assoc_left :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> Arrow0 a1
prod_assoc_left ccat0 h a b c =
  pair ccat0 h (prod ccat0 a (prod ccat0 b c)) (prod ccat0 a b) c (parallel ccat0 h a a (prod ccat0 b c) b (id0 ccat0 h a) (fst0 ccat0 h b c))
    (compose ccat0 h (prod ccat0 a (prod ccat0 b c)) (prod ccat0 b c) c (snd0 ccat0 h b c) (snd0 ccat0 h a (prod ccat0 b c)))

prod_assoc_right :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> Arrow0 a1
prod_assoc_right ccat0 h a b c =
  pair ccat0 h (prod ccat0 (prod ccat0 a b) c) a (prod ccat0 b c)
    (compose ccat0 h (prod ccat0 (prod ccat0 a b) c) (prod ccat0 a b) a (fst0 ccat0 h a b) (fst0 ccat0 h (prod ccat0 a b) c))
    (parallel ccat0 h (prod ccat0 a b) b c c (snd0 ccat0 h a b) (id0 ccat0 h c))

iso_Prod_Assoc :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> Iso0 a1
iso_Prod_Assoc ccat cmc a b c =
  Build_Iso0 (prod_assoc_left ccat cmc a b c) (prod_assoc_right ccat cmc a b c)

iso_add_unit_left :: (CCat a1) -> (CMC a1) -> a1 -> Iso0 a1
iso_add_unit_left ccat cmc a =
  Build_Iso0 (snd0 ccat cmc (unit0 ccat cmc) a) (add_unit_left ccat cmc a)

hom_Setoid :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Setoid
hom_Setoid _ _ _ _ =
  Build_Setoid

hom_Setoid_Iso :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> a1 -> a1 -> (Iso0 a1) -> (Iso0 a1) -> Iso
hom_Setoid_Iso ccat cmc a a' b b' a0 b0 =
  Build_Iso (\f -> compose ccat cmc a' a b' (compose ccat cmc a b b' (to0 ccat cmc b b' b0) f) (from0 ccat cmc a a' a0)) (\f ->
    compose ccat cmc a a' b (compose ccat cmc a' b' b (from0 ccat cmc b b' b0) f) (to0 ccat cmc a a' a0))

type Ix0 = Ix

data Ix' =
   PLeft PO_car Ix0 PO_car
 | PRight PO_car Ix0 PO_car

prodPreO :: IGT -> IGT -> PreOrder0
prodPreO _ _ =
  Build_PreOrder0

prod0 :: IGT -> IGT -> T3
prod0 x y0 =
  prodPreO x y0

pO0 :: IGT -> IGT -> T PO_car Le
pO0 x y0 =
  unsafeCoerce product (pO x) (pO y0)

loc :: IGT -> IGT -> Localized
loc x y0 a _ h1 i =
  case unsafeCoerce h1 of {
   Pair0 h2 h3 ->
    case unsafeCoerce a of {
     Pair0 sa ta ->
      case unsafeCoerce i of {
       PLeft s1 i0 t ->
        let {h = localized x sa s1 h2 i0} in
        case h of {
         ExistT x0 h0 -> ExistT (unsafeCoerce (PLeft sa x0 ta)) (\s2 h4 ->
          case unsafeCoerce s2 of {
           Pair0 su tu ->
            case unsafeCoerce h4 of {
             Pair0 h5 _ ->
              let {h6 = h0 su h5} in
              case h6 of {
               ExistT u p ->
                case p of {
                 Pair cSu downu -> ExistT (unsafeCoerce (Pair0 u t)) (Pair (unsafeCoerce (Pair0 cSu __))
                  (eq_rect_r ta
                    (case downu of {
                      Pair l l0 -> Pair (unsafeCoerce (Pair0 l (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO y0))) ta))) (unsafeCoerce (Pair0 l0 h3))}) tu))}}}})};
       PRight t i0 s1 ->
        let {h0 = localized y0 ta t h3 i0} in
        case h0 of {
         ExistT x0 h4 -> ExistT (unsafeCoerce (PRight ta x0 sa)) (\s2 h5 ->
          case unsafeCoerce s2 of {
           Pair0 su tu ->
            case unsafeCoerce h5 of {
             Pair0 h6 _ ->
              let {h7 = h4 tu h6} in
              case h7 of {
               ExistT u p ->
                case p of {
                 Pair cTu downu -> ExistT (unsafeCoerce (Pair0 s1 u)) (Pair (unsafeCoerce (Pair0 cTu __))
                  (eq_rect_r sa
                    (case downu of {
                      Pair l l0 -> Pair (unsafeCoerce (Pair0 (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO x))) (fst (Pair0 sa ta))) l))
                       (unsafeCoerce (Pair0 h2 l0))}) su))}}}})}}}}

factors :: IGT -> IGT -> PO_car -> PO_car -> (Cov a1) -> (Cov a2) -> Cov Any
factors x y0 a b h h0 =
  gCov_rect (s0 x) (\a0 _ u ->
    gCov_rect (s0 y0) (\_ _ u0 -> unsafeCoerce (Grefl (Pair0 u u0))) (\_ _ b0 l _ iHGCov ->
      unsafeCoerce (Gle_left (unsafeCoerce (Pair0 a0 b0)) (unsafeCoerce (Pair0 (le_refl (iGT_PreO x) a0) l)) (unsafeCoerce iHGCov))) (\a1 _ i _ x0 ->
      unsafeCoerce (Ginfinity (unsafeCoerce (PRight a1 i a0)) (\u0 x1 ->
        case unsafeCoerce u0 of {
         Pair0 p p0 ->
          case unsafeCoerce x1 of {
           Pair0 c _ -> eq_rect_r a0 (unsafeCoerce x0 p0 c) p}}))) b (unsafeCoerce h0)) (\_ _ b0 l _ iHGCov ->
    unsafeCoerce (Gle_left (unsafeCoerce (Pair0 b0 b)) (unsafeCoerce (Pair0 l (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO y0))) b)))
      (unsafeCoerce iHGCov))) (\a0 _ i _ x0 ->
    unsafeCoerce (Ginfinity (unsafeCoerce (PLeft a0 i b)) (\u x1 ->
      case unsafeCoerce u of {
       Pair0 p p0 ->
        case unsafeCoerce x1 of {
         Pair0 c _ -> eq_rect_r b (unsafeCoerce x0 p c) p0}}))) a (unsafeCoerce h)

type PosProd = Any

posProd_factors :: IGT -> IGT -> PO_car -> Same_set PO_car (Intersection PO_car () PosProd) Any
posProd_factors _ _ a =
  case unsafeCoerce a of {
   Pair0 x y0 ->
    let {
     x0 = \_ _ _ ->
      case same_set_iff of {
       Pair x0 _ -> x0}}
    in
    unsafeCoerce x0 __ __ __ (\x1 -> Pair (\h ->
      case h of {
       Pair0 _ p ->
        eq_rect (Pair0 x y0) (\p0 ->
          case p0 of {
           Pair0 g g0 -> Pair0 (Pair0 __ g) (Pair0 __ g0)}) x1 p}) (\h ->
      case x1 of {
       Pair0 p p0 ->
        case h of {
         Pair0 i i0 ->
          case i of {
           Pair0 _ g ->
            case i0 of {
             Pair0 _ g0 -> eq_rect (snd (Pair0 x y0)) (\g1 -> eq_rect (fst (Pair0 x y0)) (\g2 -> Pair0 __ (Pair0 g2 g1)) p g) p0 g0}}}}))}

pos0 :: IGT -> IGT -> GtPos
pos0 x y0 =
  Build_gtPos (\a b x0 x1 ->
    case unsafeCoerce a of {
     Pair0 p p0 ->
      case unsafeCoerce b of {
       Pair0 p1 p2 ->
        case unsafeCoerce x0 of {
         Pair0 l l0 ->
          case unsafeCoerce x1 of {
           Pair0 g g0 -> unsafeCoerce (Pair0 (gmono_le (s0 x) (pos x) p p1 l g) (gmono_le (s0 y0) (pos y0) p0 p2 l0 g0))}}}}) (\_ i x0 ->
    case unsafeCoerce i of {
     PLeft s1 i0 t ->
      case unsafeCoerce x0 of {
       Pair0 g g0 ->
        let {i1 = gmono_ax (s0 x) (pos x) s1 i0 g} in
        case i1 of {
         Inhabited_intro a i2 -> Inhabited_intro (unsafeCoerce (Pair0 a t))
          (case i2 of {
            Pair0 c g1 -> Pair0 (unsafeCoerce (Pair0 c __)) (unsafeCoerce (Pair0 g1 g0))})}};
     PRight t i0 s1 ->
      case unsafeCoerce x0 of {
       Pair0 g g0 ->
        let {i1 = gmono_ax (s0 y0) (pos y0) t i0 g0} in
        case i1 of {
         Inhabited_intro a i2 -> Inhabited_intro (unsafeCoerce (Pair0 s1 a))
          (case i2 of {
            Pair0 c g1 -> Pair0 (unsafeCoerce (Pair0 c __)) (unsafeCoerce (Pair0 g g1))})}}}) (\a _ x0 ->
    unsafeCoerce trans (toPreSpace (prod0 x y0)) (gCov_formtop (prod0 x y0) (pO0 x y0) (loc x y0)) a
      (let {
        x1 = \x1 a0 ->
         case gsubset_equiv (prod0 x y0) x1 a0 of {
          Pair _ x2 -> x2}}
       in
       unsafeCoerce x1 (posProd_factors x y0 a) a
         (case unsafeCoerce a of {
           Pair0 p p0 ->
            factors x y0 p p0 (unsafeCoerce gpositive (s0 x) (iGT_Pos x) p (\x2 -> Grefl (Pair0 __ x2)))
              (unsafeCoerce gpositive (s0 y0) (iGT_Pos y0) p0 (\x2 -> Grefl (Pair0 __ x2)))})) (\a0 x1 ->
      case x1 of {
       Pair0 _ p -> eq_rect_r a0 (\x2 -> unsafeCoerce x2 p) a x0}))

times :: IGT -> IGT -> IGT
times x y0 =
  Build_IGT (prod0 x y0) (pO0 x y0) (loc x y0) (pos0 x y0)

type Diagonal = Any

t_diagonal :: IGT -> T4 Diagonal
t_diagonal a =
  Build_t2 (\a0 ->
    refl (toPreSpace (s0 a)) (iGTFT a) a0 (Union_intro (Pair0 a0 a0) __ (Pair0 (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) a0)
      (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) a0)))) (\a0 b c x x0 ->
    case unsafeCoerce b of {
     Pair0 p p0 ->
      case unsafeCoerce x0 of {
       Pair0 l l0 ->
        unsafeCoerce (Pair0 (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) a0 c p x l)
          (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) a0 c p0 x l0))}}) (\a0 _ _ x x0 ->
    case unsafeCoerce x of {
     Pair0 l l0 ->
      case unsafeCoerce x0 of {
       Pair0 l1 l2 ->
        refl (toPreSpace (s0 a)) (iGTFT a) a0 (Union_intro (Pair0 a0 a0) (Pair (Pair0 l l0) (Pair0 l1 l2)) (Pair0
          (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) a0) (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) a0)))}}) (\a0 b _ x x0 ->
    gCov_rect (s0 (times a a)) (\a1 _ u a2 x1 -> refl (toPreSpace (s0 a)) (iGTFT a) a2 (Union_intro a1 u x1)) (\a1 _ b0 l _ iHX0 a2 x1 ->
      unsafeCoerce iHX0 a2
        (case unsafeCoerce a1 of {
          Pair0 p p0 ->
           case unsafeCoerce b0 of {
            Pair0 p1 p2 ->
             case unsafeCoerce l of {
              Pair0 l0 l1 ->
               case unsafeCoerce x1 of {
                Pair0 l2 l3 -> Pair0 (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) a2 p p1 l2 l0)
                 (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) a2 p0 p2 l3 l1)}}}})) (\_ _ i _ x1 a1 x2 ->
      case unsafeCoerce i of {
       PLeft s1 i0 t ->
        case unsafeCoerce x2 of {
         Pair0 l l0 ->
          let {s2 = localized a a1 s1 l i0} in
          case s2 of {
           ExistT x3 s3 ->
            unsafeCoerce (Ginfinity x3 (\u x4 ->
              let {s4 = s3 u x4} in
              case s4 of {
               ExistT x5 p ->
                case p of {
                 Pair c d ->
                  unsafeCoerce x1 (Pair0 x5 t) (Pair0 c __) u
                    (case d of {
                      Pair l1 l2 -> Pair0 l2 (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) u a1 t l1 l0)})}}))}};
       PRight t i0 s1 ->
        case unsafeCoerce x2 of {
         Pair0 l l0 ->
          let {s2 = localized a a1 t l0 i0} in
          case s2 of {
           ExistT x3 s3 ->
            unsafeCoerce (Ginfinity x3 (\u x4 ->
              let {s4 = s3 u x4} in
              case s4 of {
               ExistT x5 p ->
                case p of {
                 Pair c d ->
                  unsafeCoerce x1 (Pair0 s1 x5) (Pair0 c __) u
                    (case d of {
                      Pair l1 l2 -> Pair0 (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) u a1 s1 l1 l) l2})}}))}}}) b (unsafeCoerce x0) a0 x)

type Proj_L = Any

t_proj_L :: IGT -> IGT -> T4 Proj_L
t_proj_L a b =
  Build_t2 (\a0 ->
    refl (toPreSpace (s0 (times a b))) (iGTFT (times a b)) a0
      (case unsafeCoerce a0 of {
        Pair0 p _ -> Union_intro p __ (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) p)})) (\a0 b0 c x x0 ->
    case unsafeCoerce c of {
     Pair0 p _ ->
      case unsafeCoerce a0 of {
       Pair0 p1 _ ->
        case unsafeCoerce x of {
         Pair0 l _ -> transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) p1 p b0 l x0}}}) (\a0 _ _ x x0 ->
    case unsafeCoerce a0 of {
     Pair0 p p0 ->
      refl (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (unsafeCoerce (Pair0 p p0)) (Union_intro p (Pair x x0)
        (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) p))}) (\a0 b0 _ x x0 ->
    case unsafeCoerce a0 of {
     Pair0 p p0 ->
      gCov_rect (s0 a) (\a1 _ u p1 x1 -> refl (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (unsafeCoerce (Pair0 p1 p0)) (Union_intro a1 u x1))
        (\a1 _ b1 l _ iHX0 p1 x1 ->
        le_left (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (unsafeCoerce (Pair0 p1 p0)) (unsafeCoerce (Pair0 b1 p0))
          (unsafeCoerce (Pair0 (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO a))) p1 a1 b1 x1 l)
            (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO b))) p0))) (iHX0 b1 (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) b1)))
        (\a1 _ i _ x1 p1 x2 ->
        let {s1 = localized a p1 a1 x2 i} in
        case s1 of {
         ExistT x3 s2 ->
          unsafeCoerce (Ginfinity (unsafeCoerce (PLeft p1 x3 p0)) (\u x4 ->
            case unsafeCoerce u of {
             Pair0 p2 p3 ->
              case unsafeCoerce x4 of {
               Pair0 c _ ->
                eq_rect_r p0
                  (let {s3 = s2 p2 c} in
                   case s3 of {
                    ExistT u0 p4 ->
                     case p4 of {
                      Pair caiu downu ->
                       unsafeCoerce x1 u0 caiu p2
                         (case downu of {
                           Pair _ l0 -> l0})}}) p3}}))}) b0 (unsafeCoerce x0) p x})

type Proj_R = Any

t_proj_R :: IGT -> IGT -> T4 Proj_R
t_proj_R a b =
  Build_t2 (\a0 ->
    refl (toPreSpace (s0 (times a b))) (iGTFT (times a b)) a0
      (case unsafeCoerce a0 of {
        Pair0 _ p0 -> Union_intro p0 __ (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO b))) p0)})) (\a0 b0 c x x0 ->
    case unsafeCoerce c of {
     Pair0 _ p0 ->
      case unsafeCoerce a0 of {
       Pair0 _ p2 ->
        case unsafeCoerce x of {
         Pair0 _ l0 -> transitivity (preOrder_Transitive (preOrder_I (iGT_PreO b))) p2 p0 b0 l0 x0}}}) (\a0 _ _ x x0 ->
    case unsafeCoerce a0 of {
     Pair0 p p0 ->
      refl (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (unsafeCoerce (Pair0 p p0)) (Union_intro p0 (Pair x x0)
        (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO b))) p0))}) (\a0 b0 _ x x0 ->
    case unsafeCoerce a0 of {
     Pair0 p p0 ->
      gCov_rect (s0 b) (\a1 _ u p1 x1 -> refl (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (unsafeCoerce (Pair0 p p1)) (Union_intro a1 u x1))
        (\a1 _ b1 l _ iHX0 p1 x1 ->
        le_left (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (unsafeCoerce (Pair0 p p1)) (unsafeCoerce (Pair0 p b1))
          (unsafeCoerce (Pair0 (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO a))) p)
            (transitivity (preOrder_Transitive (preOrder_I (iGT_PreO b))) p1 a1 b1 x1 l))) (iHX0 b1 (reflexivity (preOrder_Reflexive (preOrder_I (iGT_PreO b))) b1)))
        (\a1 _ i _ x1 p1 x2 ->
        let {s1 = localized b p1 a1 x2 i} in
        case s1 of {
         ExistT x3 s2 ->
          unsafeCoerce (Ginfinity (unsafeCoerce (PRight p1 x3 p)) (\u x4 ->
            case unsafeCoerce u of {
             Pair0 p2 p3 ->
              case unsafeCoerce x4 of {
               Pair0 c _ ->
                eq_rect_r p
                  (let {s3 = s2 p3 c} in
                   case s3 of {
                    ExistT u0 p4 ->
                     case p4 of {
                      Pair caiu downu ->
                       unsafeCoerce x1 u0 caiu p3
                         (case downu of {
                           Pair _ l0 -> l0})}}) p2}}))}) b0 (unsafeCoerce x0) p0 x})

type ParallelIG f g = Any

t_parallelIG :: IGT -> IGT -> IGT -> IGT -> (T5 a1) -> (T5 a2) -> T5 (ParallelIG a1 a2)
t_parallelIG a b x y0 contF contG =
  Build_t3 (\a0 ->
    unsafeCoerce gmonotone (s0 (times a b)) a0 (\_ h ->
      case h of {
       Pair0 u u0 ->
        case u of {
         Union_intro a1 _ f ->
          case u0 of {
           Union_intro a2 _ g -> Union_intro (Pair0 a1 a2) __ (Pair0 f g)}}})
      (case unsafeCoerce a0 of {
        Pair0 p p0 ->
         unsafeCoerce monotone (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (\_ x0 -> x0) (Pair0 p p0)
           (factors a b p p0 (here0 (toPreSpace (s0 a)) (s0 x) contF p) (here0 (toPreSpace (s0 b)) (s0 y0) contG p0))})) (\a0 b0 c x0 x1 ->
    case unsafeCoerce a0 of {
     Pair0 p p0 ->
      case unsafeCoerce b0 of {
       Pair0 p1 p2 ->
        case unsafeCoerce c of {
         Pair0 p3 p4 ->
          case unsafeCoerce x0 of {
           Pair0 f g ->
            case unsafeCoerce x1 of {
             Pair0 f0 g0 ->
              let {x2 = local0 (toPreSpace (s0 a)) (s0 x) contF p p1 p3 f f0} in
              let {x3 = local0 (toPreSpace (s0 b)) (s0 y0) contG p0 p2 p4 g g0} in
              monotone (toPreSpace (s0 (times a b))) (iGTFT (times a b)) (\_ h ->
                case h of {
                 Pair0 u u0 ->
                  case u of {
                   Union_intro a1 i f1 ->
                    case u0 of {
                     Union_intro a2 i0 g1 ->
                      case i of {
                       Pair l l0 ->
                        case i0 of {
                         Pair l1 l2 -> Union_intro (Pair0 a1 a2) (Pair (Pair0 l l1) (Pair0 l0 l2)) (Pair0 f1 g1)}}}}}) (unsafeCoerce (Pair0 p p0))
                (factors a b p p0 x2 x3)}}}}}) (\a0 b0 c x0 x1 ->
    case unsafeCoerce c of {
     Pair0 p p0 ->
      case unsafeCoerce b0 of {
       Pair0 p1 p2 ->
        case unsafeCoerce a0 of {
         Pair0 p3 p4 ->
          case unsafeCoerce x0 of {
           Pair0 l l0 ->
            case unsafeCoerce x1 of {
             Pair0 f g -> unsafeCoerce (Pair0 (le_left1 (toPreSpace (s0 a)) (s0 x) contF p3 p1 p l f) (le_left1 (toPreSpace (s0 b)) (s0 y0) contG p4 p2 p0 l0 g))}}}}})
    (\a0 b0 c x0 x1 ->
    case unsafeCoerce a0 of {
     Pair0 p p0 ->
      case unsafeCoerce b0 of {
       Pair0 p1 p2 ->
        case unsafeCoerce c of {
         Pair0 p3 p4 ->
          case unsafeCoerce x0 of {
           Pair0 f g ->
            case unsafeCoerce x1 of {
             Pair0 l l0 -> unsafeCoerce (Pair0 (le_right0 (toPreSpace (s0 a)) (s0 x) contF p p1 p3 f l) (le_right0 (toPreSpace (s0 b)) (s0 y0) contG p0 p2 p4 g l0))}}}}})
    (\a0 _ j x0 ->
    case unsafeCoerce j of {
     PLeft a1 i b0 ->
      case unsafeCoerce a0 of {
       Pair0 p p0 ->
        case unsafeCoerce x0 of {
         Pair0 f g ->
          let {x1 = ax_right (toPreSpace (s0 a)) (s0 x) contF p a1 i f} in
          let {x2 = factors a b p p0 x1 (unsafeCoerce (Grefl __))} in
          unsafeCoerce gmonotone (prod0 a b) (Pair0 p p0) (\a2 x3 ->
            case unsafeCoerce a2 of {
             Pair0 _ p2 ->
              case x3 of {
               Pair0 u _ ->
                eq_rect_r p2 (\g0 _ ->
                  case u of {
                   Union_intro a3 i0 f0 -> Union_intro (Pair0 a3 b0) (Pair0 i0 __) (Pair0 f0 g0)}) p0 g x2}}) x2}};
     PRight b0 i a1 ->
      case unsafeCoerce a0 of {
       Pair0 p p0 ->
        case unsafeCoerce x0 of {
         Pair0 f g ->
          let {x1 = ax_right (toPreSpace (s0 b)) (s0 y0) contG p0 b0 i g} in
          let {x2 = factors a b p p0 (unsafeCoerce (Grefl __)) x1} in
          unsafeCoerce gmonotone (prod0 a b) (Pair0 p p0) (\a2 x3 ->
            case unsafeCoerce a2 of {
             Pair0 p1 _ ->
              case x3 of {
               Pair0 _ u ->
                eq_rect_r p1 (\f0 _ ->
                  case u of {
                   Union_intro a3 i0 g0 -> Union_intro (Pair0 a1 a3) (Pair0 i0 __) (Pair0 f0 g0)}) p f x2}}) x2}}})

type Parallel f g = ParallelIG (Sat f) (Sat g)

t_parallel :: IGT -> IGT -> IGT -> IGT -> (T4 a1) -> (T4 a2) -> T4 (Parallel a1 a2)
t_parallel a b x y0 contF contG =
  cont (toPreSpace (s0 (times a b))) (s0 (times x y0)) (iGTFT (times a b))
    (t_parallelIG a b x y0 (converse (toPreSpace (s0 a)) (s0 x) (iGT_PreO a) (iGTFT a) contF) (converse (toPreSpace (s0 b)) (s0 y0) (iGT_PreO b) (iGTFT b) contG))

proj1 :: IGT -> IGT -> Cmap
proj1 a b =
  t_proj_L a b

proj2 :: IGT -> IGT -> Cmap
proj2 a b =
  t_proj_R a b

diagonal :: IGT -> Cmap
diagonal a =
  t_diagonal a

parallel0 :: IGT -> IGT -> IGT -> IGT -> Cmap -> Cmap -> Cmap
parallel0 a b x y0 f g =
  t_parallel a b x y0 (mp_ok a x f) (mp_ok b y0 g)

pair0 :: IGT -> IGT -> IGT -> Cmap -> Cmap -> Cmap
pair0 __U0393_ a b f g =
  comp __U0393_ (times __U0393_ __U0393_) (times a b) (parallel0 __U0393_ __U0393_ a b f g) (diagonal __U0393_)

times0 :: IGT -> IGT -> IGT
times0 =
  times

type Ix1 = () -- empty inductive

ix_rect :: PreOrder0 -> PO_car -> Ix1 -> a1
ix_rect _ _ _ =
  Prelude.error "absurd case"

iBInd :: PreOrder0 -> T3
iBInd s1 =
  s1

loc0 :: PreOrder0 -> Localized
loc0 s1 _ c _ i =
  ix_rect s1 c (unsafeCoerce i)

pos1 :: PreOrder0 -> GtPos
pos1 s1 =
  gall_Pos (iBInd s1) (\_ _ -> Prelude.error "absurd case")

onePO :: PreOrder0
onePO =
  Build_PreOrder0

one :: T3
one =
  iBInd onePO

type One_intro = ()

infoBase :: PreOrder0 -> (T PO_car Le) -> IGT
infoBase a pOS =
  Build_IGT (iBInd a) pOS (loc0 a) (pos1 a)

one_PreO :: T PO_car Le
one_PreO =
  Build_t __ __

one0 :: IGT
one0 =
  infoBase (s one) one_PreO

point_mp :: IGT -> (Pt a1) -> T4 a1
point_mp a fpt =
  Build_t2 (\_ ->
    unsafeCoerce (Grefl
      (let {x = pt_here (toPreSpace (s0 a)) fpt} in
       case x of {
        Inhabited_intro a0 i -> Union_intro a0 __ i}))) (\_ _ _ _ x0 -> x0) (\_ b c x x0 ->
    unsafeCoerce (Grefl
      (let {x1 = pt_local (toPreSpace (s0 a)) fpt b c x x0} in
       case x1 of {
        Inhabited_intro a0 i ->
         case i of {
          Pair0 d f0 -> Union_intro a0 d f0}}))) (\_ b _ x x0 ->
    let {x1 = pt_cov (toPreSpace (s0 a)) fpt b x x0} in
    case x1 of {
     Inhabited_intro a0 i ->
      case i of {
       Pair0 f0 v -> unsafeCoerce (Grefl (Union_intro a0 v f0))}})

type One_intro_mp = One_intro

one_intro_mp_ok :: IGT -> T4 One_intro_mp
one_intro_mp_ok _ =
  Build_t2 (\_ -> unsafeCoerce (Grefl (Union_intro __ __ __))) __ (\_ _ _ _ _ -> unsafeCoerce (Grefl (Union_intro __ (Pair __ __) __))) (\_ _ _ _ x ->
    unsafeCoerce (Grefl
      (gCov_rect (iBInd onePO) (\_ _ u -> Union_intro __ u __) (\_ _ _ _ _ iHX -> iHX) (\_ _ i g x0 -> ix_rect onePO __ (unsafeCoerce i) g x0) __ (unsafeCoerce x))))

one_intro :: IGT -> Cmap
one_intro a = unsafeCoerce (
  one_intro_mp_ok a)

point :: IGT -> (Pt a1) -> Cmap
point a fpt =
  point_mp a (unsafeCoerce fpt)

discretePO :: PreOrder0
discretePO =
  Build_PreOrder0

discretePO0 :: T0 a1 () ()
discretePO0 =
  discrete0

discI :: IGT
discI =
  infoBase discretePO (preO (unsafeCoerce discretePO0))

covG_Cov :: PO_car -> (Cov a2) -> In PO_car a2
covG_Cov a x =
  gCov_rect (s0 discI) (\_ _ u -> unsafeCoerce u) (\a0 _ b _ _ iHX -> eq_rect_r b iHX a0) (\a0 _ i g x0 -> ix_rect discretePO a0 (unsafeCoerce i) g x0) a
    (unsafeCoerce x)

discrete1 :: IGT
discrete1 =
  Build_IGT (s0 discI) (unsafeCoerce discrete) (local1 discI) (pos1 discretePO)

fContI :: (a1 -> a2) -> T4 ()
fContI f =
  Build_t2 (\a -> unsafeCoerce (Grefl (Union_intro (unsafeCoerce f a) __ __))) __ (\a b c _ _ ->
    let {x = \_ -> eq_rect (unsafeCoerce f a) (eq_rect (unsafeCoerce f a) (Grefl (Union_intro (unsafeCoerce f a) (Pair __ __) __)) c) b} in unsafeCoerce x __)
    (\_ b _ _ x ->
    unsafeCoerce (Grefl (Union_intro b
      (gCov_rect (s0 discrete1) (\_ _ u _ -> u) (\a0 _ b0 _ _ iHX _ -> eq_rect_r b0 (\_ -> iHX __) a0 __) (\a0 _ i g x0 _ ->
        ix_rect discretePO a0 (unsafeCoerce i) g x0) b (unsafeCoerce x) __) __)))

pt_okI :: a1 -> Pt ()
pt_okI x =
  Build_pt (Inhabited_intro (unsafeCoerce x) __) (\b _ _ _ -> eq_rect_r (unsafeCoerce b) (\_ -> Inhabited_intro b (Pair0 (Pair __ __) __)) x __) (\b _ _ x0 ->
    eq_rect_r (unsafeCoerce b) (Inhabited_intro b (Pair0 __
      (gCov_rect (s0 discrete1) (\_ _ u -> u) (\a _ b0 _ _ iHX -> eq_rect_r b0 iHX a) (\_ _ _ _ _ -> Prelude.error "absurd case") b (unsafeCoerce x0)))) x)

prod_assoc_cont :: T4 ()
prod_assoc_cont =
  Build_t2 (\a -> unsafeCoerce (Grefl (Union_intro a __ __))) __ (\a b c _ _ -> eq_rect_r a (eq_rect_r a (unsafeCoerce (Grefl (Union_intro a (Pair __ __) __))) b) c)
    (\a b _ _ x -> eq_rect_r a (\x0 -> unsafeCoerce (Grefl (Union_intro a (covG_Cov a x0) __))) b x)

discrete_f :: (a1 -> a2) -> Cmap
discrete_f f =
  unsafeCoerce (fContI f)

discrete_prod_assoc :: Cmap
discrete_prod_assoc = unsafeCoerce
  prod_assoc_cont

iGT_Cat :: CCat IGT
iGT_Cat =
  times0

iGT_CMC :: CMC IGT
iGT_CMC =
  Build_CMC (\a -> unsafeCoerce id a) (\a b c -> unsafeCoerce comp a b c) one0 (\__U0393_ -> unsafeCoerce one_intro __U0393_) (\a b -> unsafeCoerce proj1 a b)
    (\a b -> unsafeCoerce proj2 a b) (\__U0393_ a b -> unsafeCoerce pair0 __U0393_ a b)

data Functor c d =
   Build_Functor (c -> d) (c -> c -> (Arrow0 c) -> Arrow0 d)

fobj :: (CCat a1) -> (CMC a1) -> (CCat a2) -> (CMC a2) -> (Functor a1 a2) -> a1 -> a2
fobj _ _ _ _ f =
  case f of {
   Build_Functor fobj0 _ -> fobj0}

fmap :: (CCat a1) -> (CMC a1) -> (CCat a2) -> (CMC a2) -> (Functor a1 a2) -> a1 -> a1 -> (Arrow0 a1) -> Arrow0 a2
fmap _ _ _ _ f =
  case f of {
   Build_Functor _ fmap0 -> fmap0}

compose_Functor :: (CCat a1) -> (CMC a1) -> (CCat a2) -> (CMC a2) -> (CCat a3) -> (CMC a3) -> (Functor a2 a3) -> (Functor a1 a2) -> Functor a1 a3
compose_Functor ccat cmcc ccat0 cmcd ccat1 cmce g f =
  Build_Functor (\x -> fobj ccat0 cmcd ccat1 cmce g (fobj ccat cmcc ccat0 cmcd f x)) (\a b x ->
    fmap ccat0 cmcd ccat1 cmce g (fobj ccat cmcc ccat0 cmcd f a) (fobj ccat cmcc ccat0 cmcd f b) (fmap ccat cmcc ccat0 cmcd f a b x))

type Adjunction c d =
  c -> d -> Iso
  -- singleton inductive, whose constructor was Build_Adjunction
  
adj_Hom_Iso :: (CCat a1) -> (CMC a1) -> (CCat a2) -> (CMC a2) -> (Functor a1 a2) -> (Functor a2 a1) -> (Adjunction a1 a2) -> a1 -> a2 -> Iso
adj_Hom_Iso _ _ _ _ _ _ a =
  a

compose_Adjunction :: (CCat a1) -> (CMC a1) -> (CCat a2) -> (CMC a2) -> (CCat a3) -> (CMC a3) -> (Functor a1 a2) -> (Functor a2 a1) -> (Functor a2 a3) -> (Functor 
                      a3 a2) -> (Adjunction a1 a2) -> (Adjunction a2 a3) -> Adjunction a1 a3
compose_Adjunction ccat cmcc ccat0 cmcd ccat1 cmce f g f' g' x x0 a b =
  iso_Trans (hom_Setoid ccat cmcc a (fobj ccat1 cmce ccat cmcc (compose_Functor ccat1 cmce ccat0 cmcd ccat cmcc g g') b))
    (hom_Setoid ccat0 cmcd (fobj ccat cmcc ccat0 cmcd f a) (fobj ccat1 cmce ccat0 cmcd g' b))
    (hom_Setoid ccat1 cmce (fobj ccat cmcc ccat1 cmce (compose_Functor ccat cmcc ccat0 cmcd ccat1 cmce f' f) a) b)
    (adj_Hom_Iso ccat cmcc ccat0 cmcd f g x a (fobj ccat1 cmce ccat0 cmcd g' b)) (adj_Hom_Iso ccat0 cmcd ccat1 cmce f' g' x0 (fobj ccat cmcc ccat0 cmcd f a) b)

data CCCOps u =
   Build_CCCOps (u -> u -> u) (u -> u -> Arrow0 u) (u -> u -> u -> (Arrow0 u) -> Arrow0 u)

func :: (CCat a1) -> (CCCOps a1) -> a1 -> a1 -> a1
func _ cCCOps =
  case cCCOps of {
   Build_CCCOps func0 _ _ -> func0}

eval :: (CCat a1) -> (CCCOps a1) -> a1 -> a1 -> Arrow0 a1
eval _ cCCOps =
  case cCCOps of {
   Build_CCCOps _ eval0 _ -> eval0}

abstract :: (CCat a1) -> (CCCOps a1) -> a1 -> a1 -> a1 -> (Arrow0 a1) -> Arrow0 a1
abstract _ cCCOps =
  case cCCOps of {
   Build_CCCOps _ _ abstract0 -> abstract0}

ap :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> a1 -> a1 -> (Arrow0 a1) -> (Arrow0 a1) -> Arrow0 a1
ap ccat cmc cccops __U0393_ a b f x =
  compose ccat cmc __U0393_ (prod ccat (func ccat cccops a b) a) b (eval ccat cccops a b) (pair ccat cmc __U0393_ (func ccat cccops a b) a f x)

postcompose :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> a1 -> a1 -> (Arrow0 a1) -> Arrow0 a1
postcompose ccat cmc cccops a a' b f =
  abstract ccat cccops (func ccat cccops a b) a' b
    (compose ccat cmc (prod ccat (func ccat cccops a b) a') (prod ccat (func ccat cccops a b) a) b (eval ccat cccops a b)
      (parallel ccat cmc (func ccat cccops a b) (func ccat cccops a b) a' a (id0 ccat cmc (func ccat cccops a b)) f))

precompose :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> a1 -> a1 -> (Arrow0 a1) -> Arrow0 a1
precompose ccat cmc cccops a b b' f =
  abstract ccat cccops (func ccat cccops a b) a b' (compose ccat cmc (prod ccat (func ccat cccops a b) a) b b' f (eval ccat cccops a b))

type Const u = Arrow0 u

multR_F :: (CCat a1) -> (CMC a1) -> a1 -> Functor a1 a1
multR_F ccat cmc c =
  Build_Functor (\x -> prod ccat x c) (\a b x -> parallel ccat cmc a b c c x (id0 ccat cmc c))

exp_F :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> Functor a1 a1
exp_F ccat cmc cccops c =
  Build_Functor (\x -> func ccat cccops c x) (\a b x -> precompose ccat cmc cccops c a b x)

eval_abstract_Iso :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> a1 -> a1 -> Iso
eval_abstract_Iso ccat cmc cccops __U0393_ a b =
  Build_Iso (\x ->
    compose ccat cmc (prod ccat __U0393_ a) (prod ccat (func ccat cccops a b) a) b (eval ccat cccops a b)
      (parallel ccat cmc __U0393_ (func ccat cccops a b) a a x (id0 ccat cmc a))) (abstract ccat cccops __U0393_ a b)

exp_adjoint :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> Adjunction a1 a1
exp_adjoint ccat cmc cccops c a b =
  eval_abstract_Iso ccat cmc cccops a c b

curry_Iso_weak :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> a1 -> a1 -> a1 -> Iso
curry_Iso_weak ccat cmc cccops a b c __U0393_ =
  let {
   x = compose_Adjunction ccat cmc ccat cmc ccat cmc (multR_F ccat cmc a) (exp_F ccat cmc cccops a) (multR_F ccat cmc b) (exp_F ccat cmc cccops b)
         (exp_adjoint ccat cmc cccops a) (exp_adjoint ccat cmc cccops b)}
  in
  iso_Trans (hom_Setoid ccat cmc __U0393_ (func ccat cccops a (func ccat cccops b c)))
    (hom_Setoid ccat cmc (fobj ccat cmc ccat cmc (compose_Functor ccat cmc ccat cmc ccat cmc (multR_F ccat cmc b) (multR_F ccat cmc a)) __U0393_) c)
    (hom_Setoid ccat cmc __U0393_ (func ccat cccops (prod ccat a b) c))
    (adj_Hom_Iso ccat cmc ccat cmc (compose_Functor ccat cmc ccat cmc ccat cmc (multR_F ccat cmc b) (multR_F ccat cmc a))
      (compose_Functor ccat cmc ccat cmc ccat cmc (exp_F ccat cmc cccops a) (exp_F ccat cmc cccops b)) x __U0393_ c)
    (iso_Trans (hom_Setoid ccat cmc (prod ccat (prod ccat __U0393_ a) b) c) (hom_Setoid ccat cmc (prod ccat __U0393_ (prod ccat a b)) c)
      (hom_Setoid ccat cmc __U0393_ (func ccat cccops (prod ccat a b) c))
      (hom_Setoid_Iso ccat cmc (prod ccat (prod ccat __U0393_ a) b) (prod ccat __U0393_ (prod ccat a b)) c c
        (iso_Sym0 ccat cmc (prod ccat __U0393_ (prod ccat a b)) (prod ccat (prod ccat __U0393_ a) b) (iso_Prod_Assoc ccat cmc __U0393_ a b)) (iso_Refl ccat cmc c))
      (iso_Sym (hom_Setoid ccat cmc __U0393_ (func ccat cccops (prod ccat a b) c)) (hom_Setoid ccat cmc (prod ccat __U0393_ (prod ccat a b)) c)
        (eval_abstract_Iso ccat cmc cccops __U0393_ (prod ccat a b) c)))

lift_weak_Iso :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (a1 -> Iso) -> Iso0 a1
lift_weak_Iso ccat cmc a b equiv =
  Build_Iso0 (to (hom_Setoid ccat cmc a a) (hom_Setoid ccat cmc a b) (equiv a) (id0 ccat cmc a))
    (from (hom_Setoid ccat cmc b a) (hom_Setoid ccat cmc b b) (equiv b) (id0 ccat cmc b))

curry_Iso :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> a1 -> a1 -> Iso0 a1
curry_Iso ccat cmc cccops a b c =
  lift_weak_Iso ccat cmc (func ccat cccops a (func ccat cccops b c)) (func ccat cccops (prod ccat a b) c) (\__U0393_ ->
    curry_Iso_weak ccat cmc cccops a b c __U0393_)

data PSh u =
   Build_PSh (u -> Setoid) (u -> u -> (Arrow0 u) -> Sty -> Sty)

psh_obj :: (CCat a1) -> (CMC a1) -> (PSh a1) -> a1 -> Setoid
psh_obj _ _ p =
  case p of {
   Build_PSh psh_obj0 _ -> psh_obj0}

psh_morph :: (CCat a1) -> (CMC a1) -> (PSh a1) -> a1 -> a1 -> (Arrow0 a1) -> Sty -> Sty
psh_morph _ _ p =
  case p of {
   Build_PSh _ psh_morph0 -> psh_morph0}

type CFunc u =
  u -> (Arrow0 u) -> Sty -> Sty
  -- singleton inductive, whose constructor was Build_CFunc
  
func_eval :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> a1 -> (CFunc a1) -> a1 -> (Arrow0 a1) -> Sty -> Sty
func_eval _ _ _ _ _ c =
  c

type NatTrns u =
  u -> Sty -> Sty
  -- singleton inductive, whose constructor was Build_NatTrns
  
nattrns :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> (NatTrns a1) -> a1 -> Sty -> Sty
nattrns _ _ _ _ n =
  n

func_Setoid :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> a1 -> Setoid
func_Setoid _ _ _ _ _ =
  Build_Setoid

cFunc_morph :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> a1 -> a1 -> (Arrow0 a1) -> (CFunc a1) -> CFunc a1
cFunc_morph ccat cmc a b __U0393_ __U0394_ ext f g ext' x =
  func_eval ccat cmc a b __U0393_ f g (compose ccat cmc g __U0394_ __U0393_ ext ext') x

func_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> PSh a1
func_PSh ccat cmc a b =
  Build_PSh (func_Setoid ccat cmc a b) (\__U0393_ __U0394_ -> unsafeCoerce cFunc_morph ccat cmc a b __U0393_ __U0394_)

prod_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> PSh a1
prod_PSh ccat cmc a b =
  Build_PSh (\__U0393_ -> prod_Setoid (psh_obj ccat cmc a __U0393_) (psh_obj ccat cmc b __U0393_)) (\__U0393_ __U0394_ f p ->
    case unsafeCoerce p of {
     Pair x y0 -> unsafeCoerce (Pair (psh_morph ccat cmc a __U0393_ __U0394_ f x) (psh_morph ccat cmc b __U0393_ __U0394_ f y0))})

y :: (CCat a1) -> (CMC a1) -> a1 -> PSh a1
y ccat cmc x =
  Build_PSh (\__U0393_ -> hom_Setoid ccat cmc __U0393_ x) (\__U0393_ __U0394_ f x0 -> compose ccat cmc __U0394_ __U0393_ x x0 f)

id_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> NatTrns a1
id_PSh _ _ _ _ x =
  x

compose_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> (PSh a1) -> (NatTrns a1) -> (NatTrns a1) -> NatTrns a1
compose_PSh ccat cmc a b c g f __U0393_ x =
  nattrns ccat cmc b c g __U0393_ (nattrns ccat cmc a b f __U0393_ x)

unit_PSh :: (CCat a1) -> (CMC a1) -> PSh a1
unit_PSh _ _ =
  Build_PSh (\_ -> unit_Setoid) (\_ _ _ x -> x)

tt_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> NatTrns a1
tt_PSh _ _ _ _ _ =
  unsafeCoerce Tt

pair_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> (PSh a1) -> (NatTrns a1) -> (NatTrns a1) -> NatTrns a1
pair_PSh ccat cmc x a b f g __U0393_ x0 =
  unsafeCoerce (Pair (nattrns ccat cmc x a f __U0393_ x0) (nattrns ccat cmc x b g __U0393_ x0))

fst_Psh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> NatTrns a1
fst_Psh _ _ _ _ _ p =
  case unsafeCoerce p of {
   Pair x _ -> x}

snd_Psh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> NatTrns a1
snd_Psh _ _ _ _ _ p =
  case unsafeCoerce p of {
   Pair _ y0 -> y0}

eval_PSh_trns :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> a1 -> Sty -> Sty
eval_PSh_trns ccat cmc a b __U0393_ x =
  case unsafeCoerce x of {
   Pair c s1 -> func_eval ccat cmc a b __U0393_ c __U0393_ (id0 ccat cmc __U0393_) s1}

eval_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> NatTrns a1
eval_PSh ccat cmc a b =
  eval_PSh_trns ccat cmc a b

abstract_PSh_trns :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> (PSh a1) -> (NatTrns a1) -> a1 -> Sty -> a1 -> (Arrow0 a1) -> Sty -> Sty
abstract_PSh_trns ccat cmc x a b f __U0393_ x0 __U0394_ x1 x2 =
  let {x3 = nattrns ccat cmc (prod_PSh ccat cmc x a) b f} in unsafeCoerce x3 __U0394_ (Pair (psh_morph ccat cmc x __U0393_ __U0394_ x1 x0) x2)

abstract_PSh_CFunc :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> (PSh a1) -> (NatTrns a1) -> a1 -> Sty -> Sty
abstract_PSh_CFunc ccat cmc x a b f __U0393_ x0 =
  unsafeCoerce abstract_PSh_trns ccat cmc x a b f __U0393_ x0

abstract_PSh :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> (PSh a1) -> (NatTrns a1) -> NatTrns a1
abstract_PSh ccat cmc x a b f =
  abstract_PSh_CFunc ccat cmc x a b f

cCat_PSh :: (CCat a1) -> (CMC a1) -> CCat (PSh a1)
cCat_PSh ccat cmc =
  prod_PSh ccat cmc

cMC_Psh :: (CCat a1) -> (CMC a1) -> CMC (PSh a1)
cMC_Psh ccat cmc =
  Build_CMC (\a -> unsafeCoerce id_PSh ccat cmc a) (\a b c -> unsafeCoerce compose_PSh ccat cmc a b c) (unit_PSh ccat cmc) (\__U0393_ ->
    unsafeCoerce tt_PSh ccat cmc __U0393_) (\a b -> unsafeCoerce fst_Psh ccat cmc a b) (\a b -> unsafeCoerce snd_Psh ccat cmc a b) (\__U0393_ a b ->
    unsafeCoerce pair_PSh ccat cmc __U0393_ a b)

cCCOps_PSh :: (CCat a1) -> (CMC a1) -> CCCOps (PSh a1)
cCCOps_PSh ccat cmc =
  Build_CCCOps (func_PSh ccat cmc) (\a b -> unsafeCoerce eval_PSh ccat cmc a b) (\__U0393_ a b -> unsafeCoerce abstract_PSh ccat cmc __U0393_ a b)

toConst :: (CCat a1) -> (CMC a1) -> (PSh a1) -> Sty -> Const (PSh a1)
toConst ccat cmc a x =
  unsafeCoerce (\__U0393_ _ -> psh_morph ccat cmc a (unit0 ccat cmc) __U0393_ (tt ccat cmc __U0393_) x)

y_Prod1 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Arrow0 (PSh a1)
y_Prod1 ccat cmc a b =
  unsafeCoerce (\__U0393_ x ->
    case unsafeCoerce x of {
     Pair a0 a1 -> pair ccat cmc __U0393_ a b a0 a1})

y_Prod2 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Arrow0 (PSh a1)
y_Prod2 ccat cmc a b =
  unsafeCoerce (\__U0393_ x ->
    unsafeCoerce (Pair (compose ccat cmc __U0393_ (prod ccat a b) a (fst0 ccat cmc a b) x) (compose ccat cmc __U0393_ (prod ccat a b) b (snd0 ccat cmc a b) x)))

y_Prod_Iso :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Iso0 (PSh a1)
y_Prod_Iso ccat cmc a b =
  Build_Iso0 (y_Prod1 ccat cmc a b) (y_Prod2 ccat cmc a b)

data Basic u =
   Basic_Base u
 | Basic_Prod u (PSh u) u (PSh u) (Basic u) (Basic u)

basic_rect :: (CCat a1) -> (CMC a1) -> (a1 -> a2) -> (a1 -> (PSh a1) -> a1 -> (PSh a1) -> (Basic a1) -> a2 -> (Basic a1) -> a2 -> a2) -> a1 -> (PSh a1) -> (Basic 
              a1) -> a2
basic_rect ccat cmc f f0 _ _ b =
  case b of {
   Basic_Base a -> f a;
   Basic_Prod a a0 b0 b1 b2 b3 -> f0 a a0 b0 b1 b2 (basic_rect ccat cmc f f0 a a0 b2) b3 (basic_rect ccat cmc f f0 b0 b1 b3)}

y_Basic_Iso :: (CCat a1) -> (CMC a1) -> a1 -> (PSh a1) -> (Basic a1) -> Iso0 (PSh a1)
y_Basic_Iso ccat cmc a a0 b =
  basic_rect ccat cmc (\a1 -> iso_Refl (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (y ccat cmc a1)) (\a1 a2 b1 b0 _ iHb1 _ iHb2 ->
    iso_Trans0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (y ccat cmc (prod ccat a1 b1)) (prod (cCat_PSh ccat cmc) (y ccat cmc a1) (y ccat cmc b1))
      (prod (cCat_PSh ccat cmc) a2 b0)
      (iso_Sym0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (prod (cCat_PSh ccat cmc) (y ccat cmc a1) (y ccat cmc b1)) (y ccat cmc (prod ccat a1 b1))
        (y_Prod_Iso ccat cmc a1 b1)) (iso_Prod (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (y ccat cmc a1) (y ccat cmc b1) a2 b0 iHb1 iHb2)) a a0 b

y_ctxt :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> PSh a1
y_ctxt ccat cmc __U0394_ a =
  Build_PSh (\__U0393_ -> hom_Setoid ccat cmc (prod ccat __U0393_ __U0394_) a) (\__U0393_ __U0393_' ext f ->
    compose ccat cmc (prod ccat __U0393_' __U0394_) (prod ccat __U0393_ __U0394_) a f
      (parallel ccat cmc __U0393_' __U0393_ __U0394_ __U0394_ ext (id0 ccat cmc __U0394_)))

data FirstOrder u =
   FO_Basic u (PSh u) (Basic u)
 | FO_Func u u u (PSh u) (PSh u) (Basic u) (FirstOrder u)

firstOrder_rect :: (CCat a1) -> (CMC a1) -> (a1 -> (PSh a1) -> (Basic a1) -> a2) -> (a1 -> a1 -> a1 -> (PSh a1) -> (PSh a1) -> (Basic a1) -> (FirstOrder a1) -> a2 ->
                   a2) -> a1 -> a1 -> (PSh a1) -> (FirstOrder a1) -> a2
firstOrder_rect ccat cmc f f0 _ _ _ f1 =
  case f1 of {
   FO_Basic a a0 b -> f a a0 b;
   FO_Func arg args ret a b b0 f2 -> f0 arg args ret a b b0 f2 (firstOrder_rect ccat cmc f f0 args ret b f2)}

y_ctxt1 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Arrow0 (PSh a1)
y_ctxt1 ccat cmc a b =
  unsafeCoerce (\__U0393_ x ->
    func_eval ccat cmc (y ccat cmc a) (y ccat cmc b) __U0393_ (unsafeCoerce x) (prod ccat __U0393_ a) (fst0 ccat cmc __U0393_ a) (snd0 ccat cmc __U0393_ a))

y_ctxt2 :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Arrow0 (PSh a1)
y_ctxt2 ccat cmc a b =
  unsafeCoerce (\__U0393_ x -> unsafeCoerce (\__U0394_ x0 x1 -> compose ccat cmc __U0394_ (prod ccat __U0393_ a) b x (pair ccat cmc __U0394_ __U0393_ a x0 x1)))

y_ctxt_Iso :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Iso0 (PSh a1)
y_ctxt_Iso ccat cmc a b =
  Build_Iso0 (y_ctxt2 ccat cmc a b) (y_ctxt1 ccat cmc a b)

y_Y_ctxt1 :: (CCat a1) -> (CMC a1) -> a1 -> Arrow0 (PSh a1)
y_Y_ctxt1 ccat cmc a =
  unsafeCoerce (\__U0393_ x -> compose ccat cmc (prod ccat __U0393_ (unit0 ccat cmc)) __U0393_ a x (fst0 ccat cmc __U0393_ (unit0 ccat cmc)))

y_Y_ctxt2 :: (CCat a1) -> (CMC a1) -> a1 -> Arrow0 (PSh a1)
y_Y_ctxt2 ccat cmc a =
  unsafeCoerce (\__U0393_ x ->
    compose ccat cmc __U0393_ (prod ccat __U0393_ (unit0 ccat cmc)) a x
      (pair ccat cmc __U0393_ __U0393_ (unit0 ccat cmc) (id0 ccat cmc __U0393_) (tt ccat cmc __U0393_)))

y_Y_ctxt_Iso :: (CCat a1) -> (CMC a1) -> a1 -> Iso0 (PSh a1)
y_Y_ctxt_Iso ccat cmc a =
  Build_Iso0 (y_Y_ctxt1 ccat cmc a) (y_Y_ctxt2 ccat cmc a)

func_Iso :: (CCat a1) -> (CMC a1) -> (PSh a1) -> (PSh a1) -> (PSh a1) -> (PSh a1) -> (Iso0 (PSh a1)) -> (Iso0 (PSh a1)) -> Iso0 (PSh a1)
func_Iso ccat cmc a a' b b' a0 b0 =
  Build_Iso0
    (compose (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a b) (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a' b)
      (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a' b')
      (precompose (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (cCCOps_PSh ccat cmc) a' b b' (to0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) b b' b0))
      (postcompose (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (cCCOps_PSh ccat cmc) a a' b (from0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) a a' a0)))
    (compose (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a' b') (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a' b)
      (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a b)
      (postcompose (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (cCCOps_PSh ccat cmc) a' a b (to0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) a a' a0))
      (precompose (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (cCCOps_PSh ccat cmc) a' b' b (from0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) b b' b0)))

firstOrder_Iso :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (PSh a1) -> (FirstOrder a1) -> Iso0 (PSh a1)
firstOrder_Iso ccat cmc args ret a fo =
  firstOrder_rect ccat cmc (\a0 a1 b ->
    iso_Trans0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) a1 (y ccat cmc a0) (y_ctxt ccat cmc (unit0 ccat cmc) a0)
      (iso_Sym0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (y ccat cmc a0) a1 (y_Basic_Iso ccat cmc a0 a1 b)) (y_Y_ctxt_Iso ccat cmc a0))
    (\arg args0 ret0 a0 b b0 _ iHfo ->
    iso_Trans0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a0 b)
      (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc (prod ccat arg args0)) (y ccat cmc ret0)) (y_ctxt ccat cmc (prod ccat arg args0) ret0)
      (iso_Trans0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a0 b)
        (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (prod (cCat_PSh ccat cmc) (y ccat cmc arg) (y ccat cmc args0)) (y ccat cmc ret0))
        (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc (prod ccat arg args0)) (y ccat cmc ret0))
        (iso_Trans0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) a0 b)
          (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc arg) (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc args0) (y ccat cmc ret0)))
          (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (prod (cCat_PSh ccat cmc) (y ccat cmc arg) (y ccat cmc args0)) (y ccat cmc ret0))
          (func_Iso ccat cmc a0 (y ccat cmc arg) b (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc args0) (y ccat cmc ret0))
            (iso_Sym0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (y ccat cmc arg) a0 (y_Basic_Iso ccat cmc arg a0 b0))
            (iso_Trans0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) b (y_ctxt ccat cmc args0 ret0)
              (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc args0) (y ccat cmc ret0)) iHfo (y_ctxt_Iso ccat cmc args0 ret0)))
          (curry_Iso (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc arg) (y ccat cmc args0) (y ccat cmc ret0)))
        (func_Iso ccat cmc (prod (cCat_PSh ccat cmc) (y ccat cmc arg) (y ccat cmc args0)) (y ccat cmc (prod ccat arg args0)) (y ccat cmc ret0) (y ccat cmc ret0)
          (y_Prod_Iso ccat cmc arg args0) (iso_Refl (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (y ccat cmc ret0))))
      (iso_Sym0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (y_ctxt ccat cmc (prod ccat arg args0) ret0)
        (func (cCat_PSh ccat cmc) (cCCOps_PSh ccat cmc) (y ccat cmc (prod ccat arg args0)) (y ccat cmc ret0)) (y_ctxt_Iso ccat cmc (prod ccat arg args0) ret0))) args
    ret a fo

yoneda_extended :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> Iso
yoneda_extended ccat cmc arg ret =
  Build_Iso (\x -> toConst ccat cmc (y_ctxt ccat cmc arg ret) x) (\x ->
    let {x0 = nattrns ccat cmc (unit_PSh ccat cmc) (y_ctxt ccat cmc arg ret) (unsafeCoerce x)} in unsafeCoerce x0 (unit0 ccat cmc) Tt)

presheaf_connection :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (PSh a1) -> (FirstOrder a1) -> Iso
presheaf_connection ccat cmc arg ret a fo =
  iso_Trans (hom_Setoid ccat cmc arg ret)
    (hom_Setoid (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc)) (y_ctxt ccat cmc arg ret))
    (hom_Setoid (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc)) a)
    (iso_Trans (hom_Setoid ccat cmc arg ret) (hom_Setoid ccat cmc (prod ccat (unit0 ccat cmc) arg) ret)
      (hom_Setoid (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc)) (y_ctxt ccat cmc arg ret))
      (hom_Setoid_Iso ccat cmc arg (prod ccat (unit0 ccat cmc) arg) ret ret (iso_Sym0 ccat cmc (prod ccat (unit0 ccat cmc) arg) arg (iso_add_unit_left ccat cmc arg))
        (iso_Refl ccat cmc ret)) (yoneda_extended ccat cmc arg ret))
    (hom_Setoid_Iso (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc)) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc))
      (y_ctxt ccat cmc arg ret) a (iso_Refl (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc)))
      (iso_Sym0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) a (y_ctxt ccat cmc arg ret) (firstOrder_Iso ccat cmc arg ret a fo)))

to_presheaf :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (PSh a1) -> (FirstOrder a1) -> (Arrow0 a1) -> Const (PSh a1)
to_presheaf ccat cmc arg ret a fo =
  to (hom_Setoid ccat cmc arg ret) (hom_Setoid (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc)) a)
    (presheaf_connection ccat cmc arg ret a fo)

from_presheaf :: (CCat a1) -> (CMC a1) -> a1 -> a1 -> (PSh a1) -> (FirstOrder a1) -> (Const (PSh a1)) -> Arrow0 a1
from_presheaf ccat cmc arg ret a fo =
  from (hom_Setoid ccat cmc arg ret) (hom_Setoid (cCat_PSh ccat cmc) (cMC_Psh ccat cmc) (unit0 (cCat_PSh ccat cmc) (cMC_Psh ccat cmc)) a)
    (presheaf_connection ccat cmc arg ret a fo)

data Member a =
   Here a (List a)
 | There a a (List a) (Member a)

member_rect :: (a1 -> (List a1) -> a2) -> (a1 -> a1 -> (List a1) -> (Member a1) -> a2 -> a2) -> a1 -> (List a1) -> (Member a1) -> a2
member_rect f f0 _ _ m =
  case m of {
   Here x xs -> f x xs;
   There x y0 ys m0 -> f0 x y0 ys m0 (member_rect f f0 x ys m0)}

member_map :: (a1 -> a2) -> a1 -> (List a1) -> (Member a1) -> Member a2
member_map f x xs elem =
  member_rect (\x0 xs0 -> Here (f x0) (map f xs0)) (\x0 y0 ys _ iHelem -> There (f x0) (f y0) (map f ys) iHelem) x xs elem

nprodT :: (CCat a1) -> (CMC a1) -> (List a1) -> a1
nprodT ccat cmc xs =
  case xs of {
   Nil -> unit0 ccat cmc;
   Cons x xs' -> prod ccat (nprodT ccat cmc xs') x}

data TermDB u =
   VarDB (List u) u (Member u)
 | ConstDB (List u) u (Arrow0 u)
 | AbsDB (List u) u u (TermDB u)
 | AppDB (List u) u u (TermDB u) (TermDB u)

termDB_rect :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> ((List a1) -> a1 -> (Member a1) -> a2) -> ((List a1) -> a1 -> (Arrow0 a1) -> a2) -> ((List a1) -> a1 -> a1 ->
               (TermDB a1) -> a2 -> a2) -> ((List a1) -> a1 -> a1 -> (TermDB a1) -> a2 -> (TermDB a1) -> a2 -> a2) -> (List a1) -> a1 -> (TermDB a1) -> a2
termDB_rect ccat cmc h f f0 f1 f2 _ _ t =
  case t of {
   VarDB g t0 m -> f g t0 m;
   ConstDB g a a0 -> f0 g a a0;
   AbsDB g dom ran t0 -> f1 g dom ran t0 (termDB_rect ccat cmc h f f0 f1 f2 (Cons dom g) ran t0);
   AppDB g dom ran t0 t1 -> f2 g dom ran t0 (termDB_rect ccat cmc h f f0 f1 f2 g (func ccat h dom ran) t0) t1 (termDB_rect ccat cmc h f f0 f1 f2 g dom t1)}

compile_DB :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> (List a1) -> a1 -> (TermDB a1) -> Arrow0 a1
compile_DB ccat cmc h __U0393_ a e =
  termDB_rect ccat cmc h (\g t m ->
    member_rect (\x xs -> snd0 ccat cmc (nprodT ccat cmc xs) x) (\x y0 ys _ iHm ->
      compose ccat cmc (prod ccat (nprodT ccat cmc ys) y0) (nprodT ccat cmc ys) x iHm (fst0 ccat cmc (nprodT ccat cmc ys) y0)) t g m) (\_ _ a0 -> a0)
    (\g dom ran _ iHe -> abstract ccat h (nprodT ccat cmc g) dom ran iHe) (\g dom ran _ iHe1 _ iHe2 -> ap ccat cmc h (nprodT ccat cmc g) dom ran iHe1 iHe2) __U0393_
    a e

data Term u var =
   Var u var
 | Const0 u (Arrow0 u)
 | Abs u u (var -> Term u var)
 | App u u (Term u var) (Term u var)

data VarEntry u var1 var2 =
   Build_varEntry u var1 var2

ty :: (VarEntry a1 a2 a3) -> a1
ty v =
  case v of {
   Build_varEntry ty0 _ _ -> ty0}

data Wf u var1 var2 =
   WfVar (List (VarEntry u var1 var2)) u var1 var2 (Member (VarEntry u var1 var2))
 | WfConst (List (VarEntry u var1 var2)) u (Arrow0 u) (Arrow0 u)
 | WfAbs (List (VarEntry u var1 var2)) u u (var1 -> Term u var1) (var2 -> Term u var2) (var1 -> var2 -> Wf u var1 var2)
 | WfApp (List (VarEntry u var1 var2)) u u (Term u var1) (Term u var1) (Term u var2) (Term u var2) (Wf u var1 var2) (Wf u var1 var2)

wf_rect :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> ((List (VarEntry a1 a2 a3)) -> a1 -> a2 -> a3 -> (Member (VarEntry a1 a2 a3)) -> a4) -> ((List
           (VarEntry a1 a2 a3)) -> a1 -> (Arrow0 a1) -> (Arrow0 a1) -> () -> a4) -> ((List (VarEntry a1 a2 a3)) -> a1 -> a1 -> (a2 -> Term a1 a2) -> (a3 -> Term 
           a1 a3) -> (a2 -> a3 -> Wf a1 a2 a3) -> (a2 -> a3 -> a4) -> a4) -> ((List (VarEntry a1 a2 a3)) -> a1 -> a1 -> (Term a1 a2) -> (Term a1 a2) -> (Term 
           a1 a3) -> (Term a1 a3) -> (Wf a1 a2 a3) -> a4 -> (Wf a1 a2 a3) -> a4 -> a4) -> (List (VarEntry a1 a2 a3)) -> a1 -> (Term a1 a2) -> (Term a1 a3) -> (Wf 
           a1 a2 a3) -> a4
wf_rect ccat cmc h f f0 f1 f2 _ _ _ _ w =
  case w of {
   WfVar g t x x' m -> f g t x x' m;
   WfConst g a e e' -> f0 g a e e' __;
   WfAbs g dom ran e1 e1' w0 -> f1 g dom ran e1 e1' w0 (\x1 x2 -> wf_rect ccat cmc h f f0 f1 f2 (Cons (Build_varEntry dom x1 x2) g) ran (e1 x1) (e1' x2) (w0 x1 x2));
   WfApp g dom ran e1 e2 e1' e2' w0 w1 ->
    f2 g dom ran e1 e2 e1' e2' w0 (wf_rect ccat cmc h f f0 f1 f2 g (func ccat h dom ran) e1 e1' w0) w1 (wf_rect ccat cmc h f f0 f1 f2 g dom e2 e2' w1)}

type Wf0 u = () -> () -> Wf u Any Any

phoas_to_DB_helper :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> (Term a1 ()) -> (Term a1 ()) -> (List (VarEntry a1 () ())) -> (Wf a1 () ()) -> TermDB a1
phoas_to_DB_helper ccat cmc h a e1 e2 __U0393_ wellformed =
  wf_rect ccat cmc h (\g t _ _ m -> VarDB (map ty g) t (member_map ty (Build_varEntry t __ __) g m)) (\g a0 e _ _ -> ConstDB (map ty g) a0
    (compose ccat cmc (nprodT ccat cmc (map ty g)) (unit0 ccat cmc) a0 e (tt ccat cmc (nprodT ccat cmc (map ty g))))) (\g dom ran _ _ _ x -> AbsDB (map ty g) dom ran
    (x __ __)) (\g dom ran _ _ _ _ _ iHwellformed1 _ iHwellformed2 -> AppDB (map ty g) dom ran iHwellformed1 iHwellformed2) __U0393_ a e1 e2 wellformed

data WfTerm u =
   Build_WfTerm (() -> Term u Any) (Wf0 u)

phoas_to_DB :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> (WfTerm a1) -> TermDB a1
phoas_to_DB ccat cmc h a e =
  case e of {
   Build_WfTerm e0 wellformed -> phoas_to_DB_helper ccat cmc h a (unsafeCoerce (e0 __)) (unsafeCoerce (e0 __)) Nil (unsafeCoerce (wellformed __ __))}

compile_phoas :: (CCat a1) -> (CMC a1) -> (CCCOps a1) -> a1 -> (WfTerm a1) -> Arrow0 a1
compile_phoas ccat cmc h a e =
  compile_DB ccat cmc h Nil a (phoas_to_DB ccat cmc h a e)

discrBinOp :: (a1 -> a2 -> a3) -> Arrow0 IGT
discrBinOp f =
  compose iGT_Cat iGT_CMC (times discrete1 discrete1) discrete1 discrete1
    (unsafeCoerce discrete_f (\p ->
      case p of {
       Pair0 x y0 -> f x y0})) (unsafeCoerce discrete_prod_assoc)

natMult :: Arrow0 IGT
natMult =
  discrBinOp mul

natAdd :: Arrow0 IGT
natAdd =
  discrBinOp add

testFunc :: Arrow0 IGT
testFunc =
  ap2 iGT_Cat iGT_CMC (prod iGT_Cat discrete1 discrete1) discrete1 discrete1 discrete1 natMult
    (ap2 iGT_Cat iGT_CMC (prod iGT_Cat discrete1 discrete1) discrete1 discrete1 discrete1 natAdd (fst0 iGT_Cat iGT_CMC discrete1 discrete1)
      (snd0 iGT_Cat iGT_CMC discrete1 discrete1)) (snd0 iGT_Cat iGT_CMC discrete1 discrete1)

add3 :: Arrow0 IGT
add3 =
  unsafeCoerce discrete_f (\n -> add n (S (S (S O))))

discrete_pt :: a1 -> Arrow0 IGT
discrete_pt x =
  unsafeCoerce point discrete1 (pt_okI x)

five :: Arrow0 IGT
five =
  discrete_pt (S (S (S (S (S O)))))

eight :: Arrow0 IGT
eight =
  compose iGT_Cat iGT_CMC one0 discrete1 discrete1 add3 five

func_1 :: Arrow0 IGT
func_1 =
  ap2 iGT_Cat iGT_CMC discrete1 discrete1 discrete1 discrete1 testFunc (ap0 iGT_Cat iGT_CMC discrete1 discrete1 eight) (id0 iGT_Cat iGT_CMC discrete1)

func_1_fo :: FirstOrder IGT
func_1_fo =
  FO_Func discrete1 (unit0 iGT_Cat iGT_CMC) discrete1 (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Basic_Base discrete1) (FO_Basic discrete1
    (y iGT_Cat iGT_CMC discrete1) (Basic_Base discrete1))

func_1_CCC :: Arrow0 (PSh IGT)
func_1_CCC =
  to_presheaf iGT_Cat iGT_CMC (prod iGT_Cat discrete1 (unit0 iGT_Cat iGT_CMC)) discrete1
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_fo
    (compose iGT_Cat iGT_CMC (prod iGT_Cat discrete1 (unit0 iGT_Cat iGT_CMC)) discrete1 discrete1 func_1 (fst0 iGT_Cat iGT_CMC discrete1 (unit0 iGT_Cat iGT_CMC)))

func1_twice :: Arrow0 (PSh IGT)
func1_twice =
  compile_phoas (cCat_PSh iGT_Cat iGT_CMC) (cMC_Psh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC)
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) (Build_WfTerm (\_ -> Abs
    (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (\x -> App (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (App
    (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (Var
    (y iGT_Cat iGT_CMC discrete1) x)))) (\_ _ -> WfAbs Nil (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (\x -> App (y iGT_Cat iGT_CMC discrete1)
    (y iGT_Cat iGT_CMC discrete1) (Const0 (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1))
    func_1_CCC) (App (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (Var
    (y iGT_Cat iGT_CMC discrete1) x))) (\x -> App (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (App
    (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (Var
    (y iGT_Cat iGT_CMC discrete1) x))) (\x1 x2 -> WfApp (Cons (Build_varEntry (y iGT_Cat iGT_CMC discrete1) x1 x2) Nil) (y iGT_Cat iGT_CMC discrete1)
    (y iGT_Cat iGT_CMC discrete1) (Const0 (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1))
    func_1_CCC) (App (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (Var
    (y iGT_Cat iGT_CMC discrete1) x1)) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (App
    (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (Var
    (y iGT_Cat iGT_CMC discrete1) x2)) (WfConst (Cons (Build_varEntry (y iGT_Cat iGT_CMC discrete1) x1 x2) Nil)
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC func_1_CCC) (WfApp (Cons
    (Build_varEntry (y iGT_Cat iGT_CMC discrete1) x1 x2) Nil) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (Var
    (y iGT_Cat iGT_CMC discrete1) x1) (Const0
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC) (Var
    (y iGT_Cat iGT_CMC discrete1) x2) (WfConst (Cons (Build_varEntry (y iGT_Cat iGT_CMC discrete1) x1 x2) Nil)
    (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) func_1_CCC func_1_CCC) (WfVar (Cons
    (Build_varEntry (y iGT_Cat iGT_CMC discrete1) x1 x2) Nil) (y iGT_Cat iGT_CMC discrete1) x1 x2 (Here (Build_varEntry (y iGT_Cat iGT_CMC discrete1) x1 x2)
    Nil))))))

discrete_fo :: FirstOrder IGT
discrete_fo =
  FO_Func discrete1 (unit0 iGT_Cat iGT_CMC) discrete1 (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1) (Basic_Base discrete1) (FO_Basic discrete1
    (y iGT_Cat iGT_CMC discrete1) (Basic_Base discrete1))

runDiscrete :: (Arrow0 IGT) -> a1
runDiscrete x =
  let {h = here (toPreSpace (s0 (unit0 iGT_Cat iGT_CMC))) (toPreSpace (s0 discrete1)) (mp_ok (unit0 iGT_Cat iGT_CMC) discrete1 (unsafeCoerce x)) __} in
  gCov_rect (iBInd onePO) (\_ _ u _ ->
    eq_rect_r __ (\u0 ->
      case unsafeCoerce u0 of {
       Union_intro a _ _ -> a}) __ u) (\_ _ _ _ h0 iHGCov _ -> eq_rect_r __ (\_ iHGCov0 -> iHGCov0 __) __ h0 iHGCov) (\_ _ i g x0 _ ->
    eq_rect_r __ (\g0 x1 -> ix_rect onePO __ (unsafeCoerce i) g0 x1) __ g x0) __ (unsafeCoerce h) __

runDiscrete_CCC :: (Const (PSh IGT)) -> a1 -> a2
runDiscrete_CCC f =
  let {
   x = from_presheaf iGT_Cat iGT_CMC (prod iGT_Cat discrete1 (unit0 iGT_Cat iGT_CMC)) discrete1
         (func (cCat_PSh iGT_Cat iGT_CMC) (cCCOps_PSh iGT_Cat iGT_CMC) (y iGT_Cat iGT_CMC discrete1) (y iGT_Cat iGT_CMC discrete1)) discrete_fo f}
  in
  (\x0 ->
  runDiscrete
    (compose iGT_Cat iGT_CMC (unit0 iGT_Cat iGT_CMC) (prod iGT_Cat discrete1 (unit0 iGT_Cat iGT_CMC)) discrete1 x
      (pair iGT_Cat iGT_CMC (unit0 iGT_Cat iGT_CMC) discrete1 (unit0 iGT_Cat iGT_CMC) (discrete_pt x0) (tt iGT_Cat iGT_CMC (unit0 iGT_Cat iGT_CMC)))))

test_computation :: Nat -> Nat
test_computation =
  runDiscrete_CCC func1_twice

