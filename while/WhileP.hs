module WhileP where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

one :: Prelude.Integer
one =
  Prelude.succ 0

sub0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub0 = (\n m -> Prelude.max 0 (n Prelude.- m))

divmod :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
          Prelude.Integer
divmod x y q u =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) q u)
    (\x' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> divmod x' y (Prelude.succ q) y)
      (\u' -> divmod x' y q u')
      u)
    x

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo = (\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)

sqrt_iter :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sqrt_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> sqrt_iter k' (Prelude.succ p) (Prelude.succ (Prelude.succ q)) (Prelude.succ (Prelude.succ q)))
      (\r' -> sqrt_iter k' p q r')
      r)
    k

sqrt :: Prelude.Integer -> Prelude.Integer
sqrt = Prelude.floor Prelude.. Prelude.sqrt Prelude.. Prelude.fromIntegral

size_induction :: (a1 -> Prelude.Integer) -> (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
size_induction f h x =
  h x (nat_rect (\_ _ -> false_rect) (\_ iHn y _ -> h y (\z _ -> iHn z __)) (f x))

complete_induction :: (Prelude.Integer -> (Prelude.Integer -> () -> a1) -> a1) -> Prelude.Integer -> a1
complete_induction =
  size_induction (\n -> n)

type Var = Prelude.Integer

data WhileP =
   WCon Var Prelude.Integer
 | WAdd Var Var Var
 | WSub Var Var Var
 | WWhile Var WhileP
 | WSeq WhileP WhileP

type State = Var -> Prelude.Integer

update :: Var -> Prelude.Integer -> State -> State
update x c s y =
  case (Prelude.==) x y of {
   Prelude.True -> c;
   Prelude.False -> s y}

goed5 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
goed5 r m =
  (Prelude.+) ((Prelude.*) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) m) r

pi15 :: Prelude.Integer -> Prelude.Integer
pi15 n =
  modulo n (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))

pi25 :: Prelude.Integer -> Prelude.Integer
pi25 r =
  div r (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))

goed :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
goed x1 x2 =
  (Prelude.+)
    (div ((Prelude.*) ((Prelude.+) x1 x2) ((Prelude.+) ((Prelude.+) x1 x2) (Prelude.succ 0))) (Prelude.succ
      (Prelude.succ 0))) x2

pi1 :: Prelude.Integer -> Prelude.Integer
pi1 z =
  let {
   w = div
         (sub
           (sqrt
             ((Prelude.+)
               ((Prelude.*) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                 (Prelude.succ (Prelude.succ 0)))))))) z) (Prelude.succ 0))) (Prelude.succ 0)) (Prelude.succ
         (Prelude.succ 0))}
  in
  sub w (sub z (div ((Prelude.+) ((Prelude.*) w w) w) (Prelude.succ (Prelude.succ 0))))

pi2 :: Prelude.Integer -> Prelude.Integer
pi2 z =
  let {
   w = div
         (sub
           (sqrt
             ((Prelude.+)
               ((Prelude.*) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
                 (Prelude.succ (Prelude.succ 0)))))))) z) (Prelude.succ 0))) (Prelude.succ 0)) (Prelude.succ
         (Prelude.succ 0))}
  in
  sub z (div ((Prelude.+) ((Prelude.*) w w) w) (Prelude.succ (Prelude.succ 0)))

goedWhileP :: WhileP -> Prelude.Integer
goedWhileP w =
  case w of {
   WCon i c -> goed5 (Prelude.succ (Prelude.succ 0)) (goed i c);
   WAdd i j k -> goed5 0 (goed i (goed j k));
   WSub i j k -> goed5 (Prelude.succ 0) (goed i (goed j k));
   WWhile i p1 -> goed5 (Prelude.succ (Prelude.succ (Prelude.succ 0))) (goed i (goedWhileP p1));
   WSeq p1 p2 ->
    goed5 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) (goed (goedWhileP p1) (goedWhileP p2))}

goedSize :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
goedSize sx1 sx2 =
  (Prelude.*) (Prelude.succ (Prelude.succ 0)) (Prelude.max sx1 sx2)

size :: Prelude.Integer -> Prelude.Integer
size x =
  complete_induction (\x0 h ->
    case (Prelude.<=) x0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
           (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) of {
     Prelude.True -> Prelude.succ 0;
     Prelude.False -> Prelude.succ
      (h
        (div x0 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) __)}) x

goedWhilePSize :: WhileP -> Prelude.Integer
goedWhilePSize w =
  case w of {
   WCon i c -> goedSize (size i) (size c);
   WAdd i j k -> goedSize (size i) (goedSize (size j) (size k));
   WSub i j k -> goedSize (size i) (goedSize (size j) (size k));
   WWhile i p1 -> goedSize (size i) (goedWhilePSize p1);
   WSeq p1 p2 -> goedSize (goedWhilePSize p1) (goedWhilePSize p2)}

whileInstruction :: WhileP -> Prelude.Integer
whileInstruction w =
  case w of {
   WWhile _ p1 -> Prelude.succ (whileInstruction p1);
   WSeq p1 p2 -> (Prelude.+) (whileInstruction p1) (whileInstruction p2);
   _ -> Prelude.succ 0}

goedInv :: Prelude.Integer -> WhileP
goedInv n =
  complete_induction (\n0 h ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> let {x = pi2 (pi25 n0)} in WAdd (pi1 (pi25 n0)) (pi1 x) (pi2 x))
      (\n1 ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> let {x = pi2 (pi25 n0)} in WSub (pi1 (pi25 n0)) (pi1 x) (pi2 x))
        (\n2 ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> WCon (pi1 (pi25 n0)) (pi2 (pi25 n0)))
          (\n3 ->
          (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
            (\_ -> WWhile (pi1 (pi25 n0)) (h (pi2 (pi25 n0)) __))
            (\n4 ->
            (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
              (\_ -> WSeq (h (pi1 (pi25 n0)) __) (h (pi2 (pi25 n0)) __))
              (\_ -> false_rec)
              n4)
            n3)
          n2)
        n1)
      (pi15 n0)) n

seqS :: (State -> Prelude.Maybe State) -> (State -> Prelude.Maybe State) -> State -> Prelude.Maybe State
seqS f g s =
  case f s of {
   Prelude.Just s' -> g s';
   Prelude.Nothing -> Prelude.Nothing}

sigma' :: (WhileP -> State -> Prelude.Maybe State) -> WhileP -> State -> Prelude.Maybe State
sigma' f c s =
  case c of {
   WCon i c0 -> Prelude.Just (update i c0 s);
   WAdd i j k -> Prelude.Just (update i ((Prelude.+) (s j) (s k)) s);
   WSub i j k -> Prelude.Just (update i (sub (s j) (s k)) s);
   WWhile i p1 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.Just s)
      (\_ -> seqS (f p1) (f (WWhile i p1)) s)
      (s i);
   WSeq p1 p2 -> seqS (f p1) (f p2) s}

sigma :: Prelude.Integer -> WhileP -> State -> Prelude.Maybe State
sigma n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ _ _ -> Prelude.Nothing)
    (\n' -> sigma' (sigma n'))
    n

wAssign :: Var -> Var -> WhileP
wAssign i j =
  WSeq (WCon i 0) (WAdd i i j)

wDec :: Var -> Var -> WhileP
wDec i tmp =
  WSeq (WCon tmp (Prelude.succ 0)) (WSub i i tmp)

wFor' :: Var -> (Var -> WhileP) -> Var -> WhileP
wFor' i p1 tmp =
  let {tmp' = Prelude.succ tmp} in WSeq (wAssign tmp i) (WWhile tmp (WSeq (wDec tmp tmp') (p1 tmp')))

wFor :: Var -> WhileP -> Var -> WhileP
wFor i p1 =
  wFor' i (\_ -> p1)

wIf0' :: Var -> (Var -> WhileP) -> (Var -> WhileP) -> Var -> WhileP
wIf0' i p1 p2 tmp =
  let {t2 = Prelude.succ tmp} in
  let {tmp' = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  WSeq (WSeq (WCon tmp (Prelude.succ 0)) (WCon t2 0)) (WSeq (WSeq
  (wFor' i (\_ -> WSeq (WCon tmp 0) (WCon t2 (Prelude.succ 0))) tmp') (wFor' tmp p1 tmp')) (wFor' t2 p2 tmp'))

wMul :: Var -> Var -> Var -> Var -> WhileP
wMul i j k tmp =
  WSeq (WSeq (wAssign tmp j) (WCon i 0)) (wFor tmp (WAdd i i k) (Prelude.succ tmp))

wPow :: Var -> Var -> Var -> Var -> WhileP
wPow i j k tmp =
  WSeq (WCon i (Prelude.succ 0)) (wFor' k (wMul i i j) tmp)

nop :: Var -> WhileP
nop tmp =
  WCon tmp 0

wAddCon :: Var -> Var -> Prelude.Integer -> Var -> WhileP
wAddCon i j c tmp =
  WSeq (WCon tmp c) (WAdd i j tmp)

wDiv :: Var -> Var -> Var -> Var -> WhileP
wDiv i j k tmp =
  let {acc = (Prelude.+) (Prelude.succ 0) tmp} in
  let {count = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  let {comp = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ 0))) tmp} in
  WSeq (WSeq (WSeq (WSeq (WCon i 0) (WCon tmp 0)) (wAssign acc j)) (WCon count 0))
  (wFor' j (\tmp2 -> WSeq (WSeq (WSeq (WSeq (wAddCon count count (Prelude.succ 0) tmp2) (WSub acc acc k))
    (wAddCon comp acc (Prelude.succ 0) tmp2)) (WSub comp comp k))
    (wIf0' comp (\tmp3 -> wIf0' tmp (\_ -> WSeq (wAssign i count) (WCon tmp (Prelude.succ 0))) nop tmp3) nop tmp2))
    ((Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) tmp))

wIfLe' :: Var -> Var -> (Prelude.Integer -> WhileP) -> (Prelude.Integer -> WhileP) -> Var -> WhileP
wIfLe' i j p1 p2 tmp =
  WSeq (WSub tmp i j) (wIf0' tmp p1 p2 (Prelude.succ tmp))

wIfLt' :: Var -> Var -> (Prelude.Integer -> WhileP) -> (Prelude.Integer -> WhileP) -> Var -> WhileP
wIfLt' i j p1 p2 tmp =
  let {tmp' = Prelude.succ tmp} in
  WSeq (WSeq (wAddCon tmp i (Prelude.succ 0) tmp') (WSub tmp tmp j)) (wIf0' tmp p1 p2 tmp')

wIfGt' :: Var -> Var -> (Prelude.Integer -> WhileP) -> (Prelude.Integer -> WhileP) -> Var -> WhileP
wIfGt' i j =
  wIfLt' j i

wIfEq' :: Var -> Var -> (Prelude.Integer -> WhileP) -> (Prelude.Integer -> WhileP) -> Var -> WhileP
wIfEq' i j p1 p2 tmp =
  let {ge = (Prelude.+) (Prelude.succ 0) tmp} in
  let {comp = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  WSeq (WSeq (WSeq (WSub tmp i j) (WSub ge j i)) (WAdd comp tmp ge))
  (wIf0' comp p1 p2 ((Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ 0))) tmp))

wIfNeq' :: Var -> Var -> (Prelude.Integer -> WhileP) -> (Prelude.Integer -> WhileP) -> Var -> WhileP
wIfNeq' i j p1 p2 =
  wIfEq' i j p2 p1

wGoed :: Var -> Var -> Var -> Var -> WhileP
wGoed i j k tmp =
  let {s1 = (Prelude.+) (Prelude.succ 0) tmp} in
  let {p = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  let {z = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ 0))) tmp} in
  let {t1 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) tmp} in
  let {tmp' = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) tmp} in
  WSeq (WSeq (WSeq (WSeq (WSeq (WAdd tmp j k) (wAddCon s1 tmp (Prelude.succ 0) tmp')) (wMul p tmp s1 tmp')) (WCon z
  (Prelude.succ (Prelude.succ 0)))) (wDiv t1 p z tmp')) (WAdd i t1 k)

wGetZ :: Var -> Var -> Var -> WhileP
wGetZ i j tmp =
  let {z2 = (Prelude.+) (Prelude.succ 0) tmp} in
  let {zi = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  let {mul = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ 0))) tmp} in
  let {ze = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) tmp} in
  let {set = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) tmp} in
  WSeq (WSeq (WSeq (wAssign tmp j) (WCon z2 (Prelude.succ (Prelude.succ 0)))) (WCon set 0))
  (wFor' tmp (\tmp2 -> WSeq
    (wIf0' set (\tmp3 -> WSeq (WSeq (WSeq (wAddCon zi tmp (Prelude.succ 0) tmp3) (wMul mul tmp zi tmp3))
      (wDiv ze mul z2 tmp3)) (wIfLe' ze j (\_ -> WSeq (wAssign i tmp) (WCon set (Prelude.succ 0))) nop tmp3)) nop
      tmp2) (wDec tmp tmp2))
    ((Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) tmp))

wPi2 :: Var -> Var -> Var -> WhileP
wPi2 i j tmp =
  let {z1 = (Prelude.+) (Prelude.succ 0) tmp} in
  let {zp = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  let {z2 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ 0))) tmp} in
  let {t2 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) tmp} in
  let {tmp' = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) tmp} in
  WSeq (WSeq (WSeq (WSeq (WSeq (wGetZ tmp j tmp') (wAddCon z1 tmp (Prelude.succ 0) tmp')) (wMul zp tmp z1 tmp'))
  (WCon z2 (Prelude.succ (Prelude.succ 0)))) (wDiv t2 zp z2 tmp')) (WSub i j t2)

wPi1 :: Var -> Var -> Var -> WhileP
wPi1 i j tmp =
  WSeq (wPi2 tmp j (Prelude.succ tmp)) (WSub i j tmp)

wPush :: Var -> Var -> Var -> WhileP
wPush s x tmp =
  let {y = (Prelude.+) (Prelude.succ 0) tmp} in
  let {tmp' = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  WSeq (WSeq (WSeq (WSeq (wPi2 tmp s tmp') (wGoed y x tmp tmp')) (wPi1 tmp s tmp'))
  (wAddCon tmp tmp (Prelude.succ 0) tmp')) (wGoed s tmp y tmp')

wPop :: Var -> Var -> WhileP
wPop s tmp =
  let {t = (Prelude.+) (Prelude.succ 0) tmp} in
  let {tmp' = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  WSeq (wPi1 tmp s tmp')
  (wIf0' tmp nop (\tmp2 -> WSeq (WSeq (WSeq (wDec tmp tmp2) (wPi2 t s tmp2)) (wPi2 t s tmp2)) (wGoed s tmp t tmp2))
    tmp')

wTop :: Var -> Var -> Var -> WhileP
wTop x s tmp =
  WSeq (wPi2 x s tmp) (wPi1 x s tmp)

wIsEmpty :: Var -> Var -> Var -> WhileP
wIsEmpty b s tmp =
  let {t = (Prelude.+) (Prelude.succ 0) tmp} in
  let {tmp' = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  WSeq (WSeq (wPi1 tmp s tmp') (WCon t 0)) (wIfGt' tmp t (\_ -> WCon b 0) (\_ -> WCon b (Prelude.succ 0)) tmp')

wGeti :: Var -> Var -> Var -> Var -> Var -> WhileP
wGeti x a i m tmp =
  let {tmp' = (Prelude.+) (Prelude.succ 0) tmp} in
  WSeq (WSeq (WSeq (WSeq (WSeq (wAssign tmp a) (wAssign x m)) (wDec x tmp')) (WSub x x i))
  (wFor' x (\tmp2 -> wPop tmp tmp2) tmp')) (wTop x tmp tmp')

wSeti :: Var -> Var -> Var -> Var -> Var -> WhileP
wSeti a i b m tmp =
  let {z = (Prelude.+) (Prelude.succ 0) tmp} in
  let {t = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  let {t2 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ 0))) tmp} in
  let {tmp' = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) tmp} in
  WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WCon z 0) (wGoed tmp z z tmp')) (wAssign t m)) (wDec t tmp'))
  (WSub t t i)) (wFor' t (\tmp2 -> WSeq (WSeq (wTop t2 a tmp2) (wPush tmp t2 tmp2)) (wPop a tmp2)) tmp'))
  (wPop a tmp')) (wPush a b tmp'))
  (wFor' t (\tmp2 -> WSeq (WSeq (wTop t2 tmp tmp2) (wPush a t2 tmp2)) (wPop tmp tmp2)) tmp')

wUniversal :: Var -> Var -> Var -> Var -> WhileP
wUniversal g m vars tmp =
  let {z = (Prelude.+) (Prelude.succ (Prelude.succ 0)) tmp} in
  let {s = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ 0))) tmp} in
  let {two = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))) tmp} in
  let {three = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))) tmp} in
  let {
   four = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
            tmp}
  in
  let {
   term = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ 0))))))) tmp}
  in
  let {
   type0 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
             (Prelude.succ (Prelude.succ 0)))))))) tmp}
  in
  let {
   t = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
         (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))) tmp}
  in
  let {
   cur = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
           (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))) tmp}
  in
  let {
   i = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
         (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))) tmp}
  in
  let {
   t2 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))) tmp}
  in
  let {
   x3 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          0))))))))))))) tmp}
  in
  let {
   x4 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ 0)))))))))))))) tmp}
  in
  let {
   x5 = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
          (Prelude.succ (Prelude.succ 0))))))))))))))) tmp}
  in
  let {
   tmp' = (Prelude.+) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
            (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))))))) tmp}
  in
  WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WCon tmp 0) (WCon z 0)) (wSeti tmp z m vars tmp'))
  (WCon s 0)) (WCon term (Prelude.succ 0))) (wAssign cur g)) (WCon one (Prelude.succ 0))) (WCon two (Prelude.succ
  (Prelude.succ 0)))) (WCon three (Prelude.succ (Prelude.succ (Prelude.succ 0))))) (WCon four (Prelude.succ
  (Prelude.succ (Prelude.succ (Prelude.succ 0)))))) (WSeq (WWhile term (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq
  (wPi1 type0 cur tmp')
  (wIf0' type0 (\tmp2 -> WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (wPi2 cur cur tmp2) (wPi1 x3 cur tmp2))
    (wPi2 t2 cur tmp2)) (wPi1 x4 t2 tmp2)) (wPi2 x5 t2 tmp2)) (wGeti t tmp x4 vars tmp2))
    (wGeti t2 tmp x5 vars tmp2)) (WAdd t t t2)) (wSeti tmp x3 t vars tmp2)) nop tmp'))
  (wIfEq' type0 one (\tmp2 -> WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (WSeq (wPi2 cur cur tmp2)
    (wPi1 x3 cur tmp2)) (wPi2 t2 cur tmp2)) (wPi1 x4 t2 tmp2)) (wPi2 x5 t2 tmp2)) (wGeti t tmp x4 vars tmp2))
    (wGeti t2 tmp x5 vars tmp2)) (WSub t t t2)) (wSeti tmp x3 t vars tmp2)) nop tmp'))
  (wIfEq' type0 two (\tmp2 -> WSeq (WSeq (WSeq (wPi2 cur cur tmp2) (wPi1 t cur tmp2)) (wPi2 t2 cur tmp2))
    (wSeti tmp t t2 vars tmp2)) nop tmp'))
  (wIfEq' type0 three (\tmp2 -> WSeq (WSeq (WSeq (wPi2 i cur tmp2) (wPi1 i i tmp2)) (wGeti t tmp i vars tmp2))
    (wIfNeq' t z (\tmp3 -> WSeq (WSeq (WSeq (wPush s cur tmp3) (wPi2 t cur tmp3)) (wPi2 t t tmp3))
      (wPush s t tmp3)) nop tmp2)) nop tmp'))
  (wIfEq' type0 four (\tmp2 -> WSeq (WSeq (WSeq (WSeq (wPi2 t cur tmp2) (wPi2 t2 t tmp2)) (wPush s t2 tmp2))
    (wPi1 t2 t tmp2)) (wPush s t2 tmp2)) nop tmp')) (wIsEmpty t s tmp'))
  (wIf0' t (\tmp2 -> WSeq (wTop cur s tmp2) (wPop s tmp2)) (\_ -> WCon term 0) tmp'))) (wGeti 0 tmp z vars tmp'))

emptyState :: Var -> Prelude.Integer
emptyState _ =
  0

wTest :: WhileP -> Prelude.Integer -> Prelude.Integer
wTest p n =
  case sigma n p emptyState of {
   Prelude.Just s -> s 0;
   Prelude.Nothing -> Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0)))))))))))))))))))))))))))))))))))))))))}

wZTestProgram :: WhileP
wZTestProgram =
  WSeq (WCon (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))))))))))))))))))))))))))))))))))))
    (wGetZ 0 (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)))

wPi1TestProgram :: WhileP
wPi1TestProgram =
  WSeq (WCon (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))))))))))))))))))))))))))))))))))))
    (wPi1 0 (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)))

wPi2TestProgram :: WhileP
wPi2TestProgram =
  WSeq (WCon (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))))))))))))))))))))))))))))))))))))
    (wPi2 0 (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)))

wGoedTestProgram :: WhileP
wGoedTestProgram =
  WSeq (WSeq (WCon (Prelude.succ 0) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))))
    (WCon (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
    (wGoed 0 (Prelude.succ 0) (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ (Prelude.succ 0))))

