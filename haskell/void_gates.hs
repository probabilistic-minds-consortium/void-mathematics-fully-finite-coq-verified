module Main where

data Fin = Fz | Fs !Fin deriving (Eq, Show)
type FinProb = (Fin, Fin)

leFin :: Fin -> Fin -> Bool
leFin Fz _ = True
leFin (Fs _) Fz = False
leFin (Fs n') (Fs m') = leFin n' m'

addFinB :: Fin -> Fin -> Fin -> (Fin, Fin)
addFinB n Fz b = (n, b)
addFinB n _ Fz = (n, Fz)
addFinB n (Fs m') (Fs b') = addFinB (Fs n) m' b'

subFin :: Fin -> Fin -> Fin -> (Fin, Fin)
subFin n Fz b = (n, b)
subFin Fz _ b = (Fz, b)
subFin _ _ Fz = (Fz, Fz)
subFin (Fs n') (Fs m') (Fs b') = subFin n' m' b'

mulFinB :: Fin -> Fin -> Fin -> (Fin, Fin)
mulFinB Fz _ b = (Fz, b)
mulFinB _ _ Fz = (Fz, Fz)
mulFinB (Fs n') m (Fs b') = let (p, b1) = mulFinB n' m b' in addFinB p m b1

divFuel :: Fin -> Fin -> Fin -> Fin -> (Fin, Fin)
divFuel Fz _ _ b = (Fz, b)
divFuel (Fs f) n m b = case (m, b) of
  (Fz, _) -> (Fz, b)
  (_, Fz) -> (Fz, Fz)
  (_, Fs b') -> if not (leFin m n) then (Fz, b')
                else let (d, b1) = subFin n m b'
                         (q, b2) = divFuel f d m b1
                     in (Fs q, b2)

divFinB :: Fin -> Fin -> Fin -> (Fin, Fin)
divFinB n m b = divFuel n n m b

fin1,fin2,fin3,fin5,fin8,fin10 :: Fin
fin1 = Fs Fz; fin2 = Fs fin1; fin3 = Fs fin2
fin5 = Fs (Fs fin3); fin8 = Fs (Fs (Fs fin5)); fin10 = Fs (Fs fin8)

clamp :: Fin -> Fin -> Fin
clamp Fz _ = fin1
clamp n d = if leFin n (case d of Fz -> Fz; Fs d' -> d') then n else case d of Fz -> Fz; Fs d' -> d'

mulProb :: FinProb -> FinProb -> Fin -> (FinProb, Fin)
mulProb p1 _ Fz = (p1, Fz)
mulProb (n1,d) (n2,_) (Fs b) = let (p,b1) = mulFinB n1 n2 b; (s,b2) = divFinB p d b1 in ((clamp s d, d), b2)

comp :: FinProb -> Fin -> (FinProb, Fin)
comp p Fz = (p, Fz)
comp (n,d) (Fs b) = let (df,b1) = subFin d n b in ((clamp df d, d), b1)

gateOr :: FinProb -> FinProb -> Fin -> (FinProb, Fin)
gateOr a _ Fz = (a, Fz)
gateOr a b (Fs b0) = let (na,b1) = comp a b0; (nb,b2) = comp b b1; (nn,b3) = mulProb na nb b2 in comp nn b3

gateNand :: FinProb -> FinProb -> Fin -> (FinProb, Fin)
gateNand a _ Fz = (a, Fz)
gateNand a b (Fs b0) = let (ab,b1) = mulProb a b b0 in comp ab b1

gateXor :: FinProb -> FinProb -> Fin -> (FinProb, Fin)
gateXor a _ Fz = (a, Fz)
gateXor a b (Fs b0) = let (o,b1) = gateOr a b b0; (n,b2) = gateNand a b b1 in mulProb o n b2

finToInt :: Fin -> Int
finToInt Fz = 0; finToInt (Fs n) = 1 + finToInt n

intToFin :: Int -> Fin
intToFin 0 = Fz; intToFin n = Fs (intToFin (n-1))

showFP :: FinProb -> String
showFP (n,d) = show (finToInt n) ++ "/" ++ show (finToInt d)

main :: IO ()
main = do
  let low = (fin2, fin10); high = (fin8, fin10); budget = intToFin 100
  putStrLn "VOID XOR Gates:"
  let test a b = let (r,rm) = gateXor a b budget in putStrLn $ "  " ++ showFP a ++ " XOR " ++ showFP b ++ " = " ++ showFP r ++ " [heat:" ++ show (100 - finToInt rm) ++ "]"
  test low low; test low high; test high low; test high high