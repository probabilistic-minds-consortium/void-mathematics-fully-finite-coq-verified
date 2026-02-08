-- void_xor.hs - VOID XOR with learning

module Main where

data Fin = Fz | Fs !Fin deriving (Eq, Ord)
data FinProb = FinProb !Fin !Fin deriving (Eq)

data World = World { wBudget :: !Fin, wHeat :: !Fin }

newtype Void a = Void { runVoid :: World -> (Maybe a, World) }

instance Functor Void where
    fmap f (Void g) = Void $ \w -> case g w of 
        (Just x, w') -> (Just (f x), w')
        (Nothing, w') -> (Nothing, w')

instance Applicative Void where
    pure x = Void $ \w -> (Just x, w)
    Void f <*> Void x = Void $ \w -> case f w of 
        (Just fn, w') -> case x w' of 
            (Just v, w'') -> (Just (fn v), w'')
            (Nothing, w'') -> (Nothing, w'')
        (Nothing, w') -> (Nothing, w')

instance Monad Void where
    return = pure
    Void x >>= f = Void $ \w -> case x w of 
        (Just v, w') -> runVoid (f v) w'
        (Nothing, w') -> (Nothing, w')

tick :: Void ()
tick = Void $ \w -> case wBudget w of
    Fz -> (Nothing, w)
    Fs b' -> (Just (), w { wBudget = b', wHeat = Fs (wHeat w) })

-- Pure arithmetic
addPure :: Fin -> Fin -> Fin
addPure a Fz = a
addPure a (Fs b) = Fs (addPure a b)

subPure :: Fin -> Fin -> Fin
subPure a Fz = a
subPure Fz _ = Fz
subPure (Fs a) (Fs b) = subPure a b

mulPure :: Fin -> Fin -> Fin
mulPure _ Fz = Fz
mulPure a (Fs Fz) = a
mulPure a (Fs b) = addPure a (mulPure a b)

divPure :: Fin -> Fin -> Fin
divPure Fz _ = Fz
divPure n d = case compareFin n d of
    LT -> Fz
    _ -> Fs (divPure (subPure n d) d)

compareFin :: Fin -> Fin -> Ordering
compareFin Fz Fz = EQ
compareFin Fz _ = LT
compareFin _ Fz = GT
compareFin (Fs a) (Fs b) = compareFin a b

-- Constants
fin0, fin1, fin2, fin3, fin4, fin5, fin6, fin7, fin8, fin9, fin10 :: Fin
fin0 = Fz
fin1 = Fs fin0
fin2 = Fs fin1
fin3 = Fs fin2
fin4 = Fs fin3
fin5 = Fs fin4
fin6 = Fs fin5
fin7 = Fs fin6
fin8 = Fs fin7
fin9 = Fs fin8
fin10 = Fs fin9

fin50, fin100, fin500, fin1000 :: Fin
fin50 = addPure (addPure fin10 fin10) (addPure fin10 (addPure fin10 fin10))
fin100 = addPure fin50 fin50
fin500 = addPure fin100 (addPure fin100 (addPure fin100 (addPure fin100 fin100)))
fin1000 = addPure fin500 fin500

-- Probability ops - one tick per operation
mulProb :: FinProb -> FinProb -> Void FinProb
mulProb (FinProb n1 d) (FinProb n2 _) = do
    tick
    let prod = mulPure n1 n2
    let scaled = divPure prod d
    let result = case scaled of { Fz -> fin1; _ -> scaled }
    pure (FinProb result d)

complement :: FinProb -> Void FinProb
complement (FinProb n d) = do
    tick
    let cn = subPure d n
    pure $ FinProb (case cn of Fz -> fin1; _ -> cn) d

-- Network
data Network = Network
    { wOR1, wOR2, wNAND1, wNAND2, wOUT1, wOUT2 :: !FinProb }

bumpUp :: FinProb -> FinProb
bumpUp (FinProb n d) = FinProb (Fs n) d

bumpDown :: FinProb -> FinProb  
bumpDown (FinProb Fz d) = FinProb Fz d
bumpDown (FinProb (Fs n) d) = FinProb n d

-- Weighted gates
weightedOR :: FinProb -> FinProb -> FinProb -> FinProb -> Void FinProb
weightedOR a b w1 w2 = do
    a' <- mulProb a w1
    b' <- mulProb b w2
    notA <- complement a'
    notB <- complement b'
    notAnotB <- mulProb notA notB
    complement notAnotB

weightedNAND :: FinProb -> FinProb -> FinProb -> FinProb -> Void FinProb
weightedNAND a b w1 w2 = do
    a' <- mulProb a w1
    b' <- mulProb b w2
    ab <- mulProb a' b'
    complement ab

weightedAND :: FinProb -> FinProb -> FinProb -> FinProb -> Void FinProb
weightedAND a b w1 w2 = do
    a' <- mulProb a w1
    b' <- mulProb b w2
    mulProb a' b'

forward :: Network -> FinProb -> FinProb -> Void FinProb
forward net a b = do
    orOut <- weightedOR a b (wOR1 net) (wOR2 net)
    nandOut <- weightedNAND a b (wNAND1 net) (wNAND2 net)
    weightedAND orOut nandOut (wOUT1 net) (wOUT2 net)

-- Error
dist :: FinProb -> FinProb -> Fin
dist (FinProb n1 _) (FinProb n2 _) = case compareFin n1 n2 of
    GT -> subPure n1 n2
    _ -> subPure n2 n1

totalError :: Network -> [(FinProb, FinProb, FinProb)] -> Void Fin
totalError _ [] = pure Fz
totalError net ((a,b,target):rest) = do
    out <- forward net a b
    let d = dist out target
    restErr <- totalError net rest
    pure (addPure d restErr)

-- Thermodynamic scan
tryWeight :: Network 
          -> (Network -> FinProb)           
          -> (FinProb -> Network -> Network) 
          -> [(FinProb, FinProb, FinProb)]
          -> Fin                             
          -> Void Network
tryWeight net getW setW examples currErr = do
    tick
    let w = getW net
    
    let netUp = setW (bumpUp w) net
    errUp <- totalError netUp examples
    
    let netDown = setW (bumpDown w) net
    errDown <- totalError netDown examples
    
    case (compareFin errUp currErr, compareFin errDown currErr) of
        (LT, _) -> pure netUp
        (_, LT) -> pure netDown
        _       -> pure net

scanEpoch :: Network -> [(FinProb, FinProb, FinProb)] -> Void Network
scanEpoch net examples = do
    tick
    err0 <- totalError net examples
    
    net1 <- tryWeight net wOR1   (\w n -> n { wOR1 = w })   examples err0
    err1 <- totalError net1 examples
    
    net2 <- tryWeight net1 wOR2   (\w n -> n { wOR2 = w })   examples err1
    err2 <- totalError net2 examples
    
    net3 <- tryWeight net2 wNAND1 (\w n -> n { wNAND1 = w }) examples err2
    err3 <- totalError net3 examples
    
    net4 <- tryWeight net3 wNAND2 (\w n -> n { wNAND2 = w }) examples err3
    err4 <- totalError net4 examples
    
    net5 <- tryWeight net4 wOUT1  (\w n -> n { wOUT1 = w })  examples err4
    err5 <- totalError net5 examples
    
    net6 <- tryWeight net5 wOUT2  (\w n -> n { wOUT2 = w })  examples err5
    
    pure net6

countCorrect :: Network -> [(FinProb, FinProb, FinProb)] -> Void Fin
countCorrect _ [] = pure Fz
countCorrect net ((a,b,target):rest) = do
    out <- forward net a b
    let d = dist out target
    restCount <- countCorrect net rest
    pure $ if compareFin d fin3 == LT then Fs restCount else restCount

trainLoop :: Fin -> Network -> [(FinProb, FinProb, FinProb)] -> Void (Network, Fin)
trainLoop Fz net _ = pure (net, Fz)
trainLoop (Fs epochs) net examples = do
    tick
    net' <- scanEpoch net examples
    correct <- countCorrect net' examples
    case correct of
        Fs (Fs (Fs (Fs Fz))) -> pure (net', correct)
        _ -> trainLoop epochs net' examples

-- Boundary
boundary_finToInt :: Fin -> Int
boundary_finToInt Fz = 0
boundary_finToInt (Fs n) = 1 + boundary_finToInt n

boundary_finProbToStr :: FinProb -> String
boundary_finProbToStr (FinProb n d) = show (boundary_finToInt n) ++ "/" ++ show (boundary_finToInt d)

showNet :: Network -> String
showNet n = "OR[" ++ boundary_finProbToStr (wOR1 n) ++ "," ++ boundary_finProbToStr (wOR2 n) ++ "] " ++
            "NAND[" ++ boundary_finProbToStr (wNAND1 n) ++ "," ++ boundary_finProbToStr (wNAND2 n) ++ "] " ++
            "OUT[" ++ boundary_finProbToStr (wOUT1 n) ++ "," ++ boundary_finProbToStr (wOUT2 n) ++ "]"

-- Main
main :: IO ()
main = do
    putStrLn "========================================================"
    putStrLn "   VOID XOR - Thermodynamic Scan Learning"
    putStrLn "========================================================"
    putStrLn ""
    
    let low = FinProb fin2 fin10
    let high = FinProb fin8 fin10
    
    let initNet = Network
            (FinProb fin5 fin10) (FinProb fin5 fin10)
            (FinProb fin5 fin10) (FinProb fin5 fin10)
            (FinProb fin5 fin10) (FinProb fin5 fin10)
    
    let examples = [(low, low, low), (low, high, high), (high, low, high), (high, high, low)]
    
    putStrLn $ "Initial: " ++ showNet initNet
    putStrLn ""
    
    let budget = fin10000
    let epochs = fin50
    let world = World budget Fz
    
    let (result, world') = runVoid (trainLoop epochs initNet examples) world
    
    case result of
        Nothing -> putStrLn "EXHAUSTED"
        Just (finalNet, correct) -> do
            putStrLn $ "Final: " ++ showNet finalNet
            putStrLn $ "Correct: " ++ show (boundary_finToInt correct) ++ "/4"
            putStrLn ""
            putStrLn "Testing:"
            testNet finalNet examples
            putStrLn ""
            putStrLn $ "Heat: " ++ show (boundary_finToInt (wHeat world'))

testNet :: Network -> [(FinProb, FinProb, FinProb)] -> IO ()
testNet net examples = mapM_ test examples
  where
    test (a, b, target) = do
        let world = World fin100 Fz
        let (result, _) = runVoid (forward net a b) world
        case result of
            Nothing -> putStrLn "  EXHAUSTED"
            Just out -> do
                let d = dist out target
                let mark = if compareFin d fin3 == LT then "✓" else "✗"
                putStrLn $ "  " ++ boundary_finProbToStr a ++ " XOR " ++ 
                           boundary_finProbToStr b ++ " = " ++ 
                           boundary_finProbToStr out ++ 
                           " (target: " ++ boundary_finProbToStr target ++ ") " ++ mark

trainLoop :: Fin -> Network -> [(FinProb, FinProb, FinProb)] -> Fin -> Void (Network, Fin, Fin)
trainLoop Fz net _ epochsDone = pure (net, Fz, epochsDone)
trainLoop (Fs epochs) net examples epochsDone = do
    tick
    net' <- scanEpoch net examples
    correct <- countCorrect net' examples
    case correct of
        Fs (Fs (Fs (Fs Fz))) -> pure (net', correct, epochsDone)
        _ -> trainLoop epochs net' examples (Fs epochsDone)