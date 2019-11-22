import WhileP

instance Show WhileP where
  show (WAdd i j k) = "x" ++ show i ++ " := x" ++ show j ++ " + x" ++ show k
  show (WSub i j k) = "x" ++ show i ++ " := x" ++ show j ++ " - x" ++ show k
  show (WCon i c) = "x" ++ show i ++ " := " ++ show c
  show (WSeq p1 p2) = show p1 ++ ";\n" ++ show p2
  show (WWhile i p1) = "whileP x" ++ show i ++ " != 0 do\n" ++ show p1 ++ "\nod"

inverse = do
  Prelude.print (goedWhileP (WCon 0 42))
  putStrLn ""
  Prelude.print (goedInv 42)
  putStrLn ""
  Prelude.print (goedInv 1337)
  putStrLn ""
  Prelude.print (goedInv 12312421312)
  putStrLn ""
  Prelude.print (goedWhileP (WSeq (WCon 2 42) (WAdd 1 2 3)))
  Prelude.print (goedInv (goedWhileP (WSeq (WCon 2 42) (WAdd 1 2 3))))
  putStrLn ""
  Prelude.print (goedInv 961827193)
  putStrLn ""
  Prelude.print (goedInv 9999)
  putStrLn ""
  Prelude.print (goedInv 999888)
  putStrLn ""
  Prelude.print (goedInv 999999999888888887777777666666555554)

sizeEstimate = do
  Prelude.print (goedWhileP (WAdd 1 2 3))
  Prelude.putStrLn ("add: " ++ show (goedWhilePSize (WAdd 1 2 3)))
  Prelude.putStrLn ("mul: " ++ show (goedWhilePSize (wMul 0 1 2 3)))
  Prelude.putStrLn ("div: " ++ show (goedWhilePSize (wDiv 0 1 2 3)))
  Prelude.putStrLn ("pow: " ++ show (goedWhilePSize (wPow 0 1 2 3)))
  Prelude.putStrLn ("goed: " ++ show (goedWhilePSize wGoedTestProgram))
  Prelude.putStrLn ("pi2: " ++ show (goedWhilePSize wPi2TestProgram))
  Prelude.putStrLn ("pi1: " ++ show (goedWhilePSize wPi1TestProgram))
-- 1040
-- add: 4
-- mul: 128
-- div: 2097152
-- pow: 2048
-- goed: 33554432
-- pi2: 2199023255552
-- pi1: 4398046511104

univ = do
  Prelude.putStrLn ("Instructions: " ++ show (whileInstruction (wUniversal 0 1 2 3)))
  Prelude.putStrLn ("Size: " ++ show (goedWhilePSize (wUniversal 0 1 2 3)))
  -- Instructions: 32630
  -- Size: 18889465931478580854784
  -- Size: 18.889.465.931.478.580.854.784
  -- Size:
  -- 18 Triliarde (ZB)
  -- 889 Trillionen (EB)
  -- 465 Billiarden (PB)
  -- 931 Billionen (TB)
  -- 478 Milliarden (GB)
  -- 580 Millionen (MB)
  -- 854 Tausend (KB)
  -- 784

main = univ
