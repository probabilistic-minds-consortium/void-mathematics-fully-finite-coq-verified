-- void_perceptron.hs - VOID NEURAL NETWORK
-- Pure finite. No infinity. No cheating.
--
-- ARCHITECTURE:
--   PURE VOID (Sections 1-8): Zero Int, all operations paid, bounded structures
--   BOUNDARY  (Section 9):    Haskell I/O metalanguage

module Main where

-- ============================================================================
-- PART I: PURE VOID
-- ============================================================================

-- ============================================================================
-- 1. ONTOLOGIA
-- ============================================================================

data Fin = Fz | Fs !Fin deriving (Eq, Ord)

data FinProb = FinProb !Fin !Fin deriving (Eq)

data Bool3 = BTrue | BFalse | BUnknown deriving (Eq)

data Error = Undershoot | Match | Overshoot deriving (Eq)

-- ============================================================================
-- 2. BOUNDED STRUCTURES
-- ============================================================================

data BList a = BList !Fin ![a]  -- (capacity, items)

bEmpty :: Fin -> BList a
bEmpty cap = BList cap []

-- ============================================================================
-- 3. TERMODYNAMIKA
-- ============================================================================

data World = World 
    { wBudget :: !Fin
    , wHeat   :: !Fin
    }

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

-- ============================================================================
-- 4. ARYTMETYKA PŁATNA (wszystko z fuel)
-- ============================================================================

succV :: Fin -> Void Fin
succV n = tick >> return (Fs n)

predV :: Fin -> Void Fin
predV Fz = tick >> return Fz
predV (Fs n) = tick >> return n

addV :: Fin -> Fin -> Fin -> Void Fin
addV Fz _ _ = pure Fz  -- fuel wyczerpany
addV _ a Fz = pure a
addV (Fs fuel) a (Fs b) = tick >> addV fuel (Fs a) b

subV :: Fin -> Fin -> Fin -> Void Fin
subV Fz _ _ = pure Fz
subV _ a Fz = pure a
subV _ Fz _ = pure Fz
subV (Fs fuel) (Fs a) (Fs b) = tick >> subV fuel a b

ltV :: Fin -> Fin -> Fin -> Void Bool3
ltV Fz _ _ = pure BUnknown  -- fuel wyczerpany
ltV _ Fz (Fs _) = tick >> pure BTrue
ltV _ Fz Fz = tick >> pure BFalse
ltV _ (Fs _) Fz = tick >> pure BFalse
ltV (Fs fuel) (Fs a) (Fs b) = tick >> ltV fuel a b

gtV :: Fin -> Fin -> Fin -> Void Bool3
gtV fuel a b = ltV fuel b a

eqV :: Fin -> Fin -> Fin -> Void Bool3
eqV Fz _ _ = pure BUnknown
eqV _ Fz Fz = tick >> pure BTrue
eqV _ Fz (Fs _) = tick >> pure BFalse
eqV _ (Fs _) Fz = tick >> pure BFalse
eqV (Fs fuel) (Fs a) (Fs b) = tick >> eqV fuel a b

-- ============================================================================
-- 5. OPERACJE NA BList (wszystko płatne z fuel)
-- ============================================================================

-- Zip dwóch BList - płatne
bZip :: Fin -> BList a -> BList b -> Void (BList (a, b))
bZip Fz _ _ = pure (bEmpty Fz)
bZip _ (BList _ []) _ = pure (bEmpty Fz)
bZip _ _ (BList _ []) = pure (bEmpty Fz)
bZip (Fs fuel) (BList cap1 (x:xs)) (BList cap2 (y:ys)) = do
    tick
    BList capRest rest <- bZip fuel (BList cap1 xs) (BList cap2 ys)
    pure (BList (Fs capRest) ((x, y) : rest))

-- Map z fuel - płatne
bMapV :: Fin -> (a -> Void b) -> BList a -> Void (BList b)
bMapV Fz _ (BList cap _) = pure (BList cap [])
bMapV _ _ (BList cap []) = pure (BList cap [])
bMapV (Fs fuel) f (BList cap (x:xs)) = do
    tick
    y <- f x
    BList _ ys <- bMapV fuel f (BList cap xs)
    pure (BList cap (y : ys))

-- Fold z fuel - płatne
bFoldV :: Fin -> (b -> a -> Void b) -> b -> BList a -> Void b
bFoldV Fz _ acc _ = pure acc
bFoldV _ _ acc (BList _ []) = pure acc
bFoldV (Fs fuel) f acc (BList cap (x:xs)) = do
    tick
    acc' <- f acc x
    bFoldV fuel f acc' (BList cap xs)

-- Licznik poprawnych (jako Fin, nie Int!)
bCountIf :: Fin -> (a -> Void Bool3) -> BList a -> Void Fin
bCountIf Fz _ _ = pure Fz
bCountIf _ _ (BList _ []) = pure Fz
bCountIf (Fs fuel) pred (BList cap (x:xs)) = do
    tick
    result <- pred x
    restCount <- bCountIf fuel pred (BList cap xs)
    case result of
        BTrue -> succV restCount
        _ -> pure restCount

-- ============================================================================
-- 6. STAŁE JAKO Fin
-- ============================================================================

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

addPure :: Fin -> Fin -> Fin
addPure a Fz = a
addPure a (Fs b) = Fs (addPure a b)

fin20 :: Fin
fin20 = addPure fin10 fin10

fin50 :: Fin
fin50 = addPure fin20 (addPure fin20 fin10)

fin100 :: Fin
fin100 = addPure fin50 fin50

fin500 :: Fin
fin500 = addPure fin100 (addPure fin100 (addPure fin100 (addPure fin100 fin100)))

fin1000 :: Fin
fin1000 = addPure fin500 fin500

fin10000 :: Fin
fin10000 = addPure fin1000 (addPure fin1000 (addPure fin1000 (addPure fin1000 
           (addPure fin1000 (addPure fin1000 (addPure fin1000 
           (addPure fin1000 (addPure fin1000 fin1000))))))))

-- Standard fuel
stdFuel :: Fin
stdFuel = fin100

-- ============================================================================
-- 7. SYNAPSA I NEURON
-- ============================================================================

data Synapse = Synapse 
    { conductance :: !FinProb
    }

data Neuron = Neuron 
    { synapses  :: !(BList Synapse)
    , threshold :: !Fin
    }

-- Transmisja przez synapsę - płatna
transmit :: Fin -> Fin -> Synapse -> Void (Fin, Fin)  -- (signal, heat)
transmit _ Fz _ = pure (Fz, Fz)  -- brak inputu
transmit fuel input (Synapse (FinProb num den)) = do
    tick
    halfDen <- subV fuel den fin5
    isOpen <- gtV fuel num halfDen
    case isOpen of
        BTrue -> pure (input, Fz)
        _ -> do
            resistance <- subV fuel den num
            pure (Fz, resistance)

-- Aktywacja neuronu - płatna
activate :: Fin -> Neuron -> BList Fin -> Void (Fin, Fin, BList Fin)
activate fuel neuron inputs = do
    tick
    -- Zip inputs z synapsami
    pairs <- bZip fuel inputs (synapses neuron)
    
    -- Transmit przez każdą parę
    results <- bMapV fuel (\(i, s) -> transmit fuel i s) pairs
    
    -- Wyodrębnij sygnały i ciepło
    signals <- bMapV fuel (\(sig, _) -> pure sig) results
    heats <- bMapV fuel (\(_, h) -> pure h) results
    
    -- Sumuj sygnały
    totalSignal <- bFoldV fuel (\acc s -> addV fuel acc s) Fz signals
    
    -- Sumuj ciepło
    totalHeat <- bFoldV fuel (\acc h -> addV fuel acc h) Fz heats
    
    -- Porównaj z progiem
    aboveThreshold <- gtV fuel totalSignal (threshold neuron)
    
    let output = case aboveThreshold of
            BTrue -> Fs Fz
            _ -> Fz
    
    pure (output, totalHeat, signals)

-- ============================================================================
-- 8. UCZENIE - CREDIT PROPAGATION
-- ============================================================================

-- Oblicz błąd - płatne
computeError :: Fin -> Fin -> Fin -> Void Error
computeError fuel output target = do
    tick
    outIsZero <- eqV fuel output Fz
    targIsZero <- eqV fuel target Fz
    case (outIsZero, targIsZero) of
        (BTrue, BTrue)   -> pure Match
        (BFalse, BFalse) -> pure Match
        (BTrue, BFalse)  -> pure Undershoot
        (BFalse, BTrue)  -> pure Overshoot
        _ -> pure Match  -- BUnknown case

-- Poszerz rurę - płatne
erode :: Fin -> Synapse -> Void Synapse
erode fuel (Synapse (FinProb n d)) = do
    tick
    maxN <- subV fuel d fin1
    isMax <- gtV fuel n maxN
    case isMax of
        BTrue -> pure $ Synapse (FinProb n d)
        _ -> do
            n' <- succV n
            pure $ Synapse (FinProb n' d)

-- Zwęź rurę - płatne
constrict :: Fin -> Synapse -> Void Synapse
constrict fuel (Synapse (FinProb n d)) = do
    tick
    isMin <- ltV fuel n fin2
    case isMin of
        BTrue -> pure $ Synapse (FinProb fin1 d)
        _ -> do
            n' <- predV n
            pure $ Synapse (FinProb n' d)

-- Credit propagation - płatne
propagateCredit :: Fin -> Error -> BList (Fin, Synapse) -> Void (BList Synapse)
propagateCredit fuel err pairs = do
    tick
    bMapV fuel updateOne pairs
  where
    updateOne (Fz, s) = pure s  -- nieaktywny input
    updateOne (_, s) = case err of
        Undershoot -> erode fuel s
        Match      -> erode fuel s
        Overshoot  -> constrict fuel s

-- Krok treningowy - płatne
trainStep :: Fin -> Neuron -> BList Fin -> Fin -> Void (Neuron, Fin, Fin, Error)
trainStep fuel neuron inputs target = do
    tick
    -- Forward
    (output, heatGen, _) <- activate fuel neuron inputs
    
    -- Error
    err <- computeError fuel output target
    
    -- Credit propagation
    pairs <- bZip fuel inputs (synapses neuron)
    newSynapses <- propagateCredit fuel err pairs
    
    let newNeuron = neuron { synapses = newSynapses }
    pure (newNeuron, output, heatGen, err)

-- ============================================================================
-- 9. TRENING - PEŁNA EPOKA
-- ============================================================================

data Example = Example 
    { exInputs :: !(BList Fin)
    , exTarget :: !Fin
    }

data TrainResult = TrainResult
    { trNeuron  :: !Neuron
    , trCorrect :: !Fin
    }

-- Trenuj na jednym przykładzie
trainOne :: Fin -> Neuron -> Example -> Void (Neuron, Bool3)
trainOne fuel neuron ex = do
    (newNeuron, output, _, _) <- trainStep fuel neuron (exInputs ex) (exTarget ex)
    isCorrect <- eqV fuel output (exTarget ex)
    pure (newNeuron, isCorrect)

-- Trenuj epokę (fold po BList przykładów)
trainEpoch :: Fin -> Neuron -> BList Example -> Void TrainResult
trainEpoch fuel neuron examples = do
    tick
    bFoldV fuel step (TrainResult neuron Fz) examples
  where
    step (TrainResult n correct) ex = do
        (newN, isCorr) <- trainOne fuel n ex
        newCorrect <- case isCorr of
            BTrue -> succV correct
            _ -> pure correct
        pure (TrainResult newN newCorrect)

-- Trenuj wiele epok (z fuel jako licznik)
trainLoop :: Fin -> Fin -> Neuron -> BList Example -> Fin -> Void (Neuron, Fin, Bool3)
trainLoop Fz _ neuron _ lastCorrect = pure (neuron, Fz, BFalse)  -- fuel wyczerpany
trainLoop (Fs epochsLeft) fuel neuron examples _ = do
    tick
    TrainResult newNeuron correct <- trainEpoch fuel neuron examples
    
    -- Sprawdź czy wszystkie poprawne (4 = fin4)
    allCorrect <- eqV fuel correct fin4
    case allCorrect of
        BTrue -> pure (newNeuron, correct, BTrue)  -- sukces!
        _ -> trainLoop epochsLeft fuel newNeuron examples correct

-- ============================================================================
-- PART II: BOUNDARY
-- ============================================================================

-- ============================================================================
-- 10. BOUNDARY: I/O INTERFACE
-- ============================================================================

-- Gdy Fin = 10000, po 10000 iteracjach trafiamy na go 0 _ = -1
-- Wynik: 10000 + (-1) = 9999

boundary_finToInt :: Fin -> Int
boundary_finToInt = go 10001  -- ← zmień na 10001
  where
    go 0 _ = -1
    go _ Fz = 0
    go limit (Fs n) = 1 + go (limit - 1) n

boundary_finProbToStr :: FinProb -> String
boundary_finProbToStr (FinProb n d) = 
    show (boundary_finToInt n) ++ "/" ++ show (boundary_finToInt d)

boundary_showSynapses :: BList Synapse -> String
boundary_showSynapses (BList _ syns) = 
    "[" ++ go syns ++ "]"
  where
    go [] = ""
    go [s] = boundary_finProbToStr (conductance s)
    go (s:ss) = boundary_finProbToStr (conductance s) ++ ", " ++ go ss

boundary_bool3ToStr :: Bool3 -> String
boundary_bool3ToStr BTrue = "Yes"
boundary_bool3ToStr BFalse = "No"
boundary_bool3ToStr BUnknown = "Unknown"

-- ============================================================================
-- 11. MAIN
-- ============================================================================

main :: IO ()
main = do
    putStrLn "========================================================"
    putStrLn "     VOID PERCEPTRON: Pure Finite Learning"
    putStrLn ""
    putStrLn "  No floats. No infinity. No cheating."
    putStrLn "========================================================"
    putStrLn ""
    
    let budget = fin10000
    let fuel = fin100
    let epochs = fin20
    
    -- Inicjalizacja: 2 synapsy, conductance 3/10
    let initSyn = Synapse (FinProb fin3 fin10)
    let initSynapses = BList fin2 [initSyn, initSyn]
    let neuron = Neuron initSynapses fin1
    
    -- Dataset AND (jako BList)
    let ex1 = Example (BList fin2 [Fz, Fz]) Fz
    let ex2 = Example (BList fin2 [Fz, Fs Fz]) Fz
    let ex3 = Example (BList fin2 [Fs Fz, Fz]) Fz
    let ex4 = Example (BList fin2 [Fs Fz, Fs Fz]) (Fs Fz)
    let dataset = BList fin4 [ex1, ex2, ex3, ex4]
    
    putStrLn $ "Initial conductance: " ++ boundary_showSynapses initSynapses
    putStrLn $ "Budget: " ++ show (boundary_finToInt budget)
    putStrLn ""
    
    let world = World budget Fz
    let (result, world') = runVoid (trainLoop epochs fuel neuron dataset Fz) world
    
    case result of
        Nothing -> do
            putStrLn "BUDGET EXHAUSTED"
            putStrLn $ "Heat: " ++ show (boundary_finToInt (wHeat world'))
        Just (finalNeuron, correct, learned) -> do
            putStrLn $ "Final conductance: " ++ boundary_showSynapses (synapses finalNeuron)
            putStrLn $ "Correct: " ++ show (boundary_finToInt correct) ++ "/4"
            putStrLn $ "Learned AND: " ++ boundary_bool3ToStr learned
            putStrLn ""
            putStrLn "========================================================"
            putStrLn $ "Budget remaining: " ++ show (boundary_finToInt (wBudget world'))
            putStrLn $ "Heat generated: " ++ show (boundary_finToInt (wHeat world'))
            let conserved = boundary_finToInt (wBudget world') + boundary_finToInt (wHeat world')
            putStrLn $ "Conservation: " ++ show conserved ++ " = " ++ show (boundary_finToInt budget)