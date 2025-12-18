-- void_xor.hs - THE VOID MULTILAYER PERCEPTRON
-- "We are going to hit the wall."
-- XOR Gate via Thermodynamic Backpressure.

module Main where

-- ============================================================================
-- 1. ONTOLOGIA I FIZYKA (Standard VOID)
-- ============================================================================

data Fin = Fz | Fs !Fin deriving (Eq, Ord)
data FinProb = FinProb !Fin !Fin deriving (Eq)
data Bool3 = BTrue | BFalse | BUnknown deriving (Eq)
data Error = Undershoot | Match | Overshoot deriving (Eq, Show)

-- BOUNDED LIST
data BList a = BList !Fin ![a]

-- FIZYKA
data World = World { wBudget :: !Fin, wHeat :: !Fin }
newtype Void a = Void { runVoid :: World -> (Maybe a, World) }

instance Functor Void where fmap f (Void g) = Void $ \w -> case g w of (Just x, w') -> (Just (f x), w'); _ -> (Nothing, w)
instance Applicative Void where pure x = Void $ \w -> (Just x, w); Void f <*> Void x = Void $ \w -> case f w of (Just fn, w') -> (case x w' of (Just v, w'') -> (Just (fn v), w''); _ -> (Nothing, w'')); _ -> (Nothing, w)
instance Monad Void where return = pure; Void x >>= f = Void $ \w -> case x w of (Just v, w') -> runVoid (f v) w'; _ -> (Nothing, w)

tick :: Void ()
tick = Void $ \w -> case wBudget w of Fz -> (Nothing, w); Fs b' -> (Just (), w { wBudget = b', wHeat = Fs (wHeat w) })

-- ARYTMETYKA (Z fuel)
succV n = tick >> return (Fs n)
predV Fz = tick >> return Fz; predV (Fs n) = tick >> return n
ltV Fz (Fs _) = tick >> return BTrue; ltV _ Fz = tick >> return BFalse; ltV (Fs a) (Fs b) = tick >> ltV a b
gtV a b = ltV b a
subV Fz _ = pure Fz; subV a Fz = pure a; subV (Fs a) (Fs b) = tick >> subV a b

-- LIST UTILS
bZip (Fs f) (BList c1 (x:xs)) (BList c2 (y:ys)) = tick >> (bZip f (BList c1 xs) (BList c2 ys)) >>= \(BList cr rs) -> pure (BList (Fs cr) ((x,y):rs))
bZip _ _ _ = pure (BList Fz [])

bMapV (Fs f) func (BList c (x:xs)) = tick >> func x >>= \y -> bMapV f func (BList c xs) >>= \(BList _ ys) -> pure (BList c (y:ys))
bMapV _ _ (BList c []) = pure (BList c [])

bFoldV (Fs f) func acc (BList _ (x:xs)) = tick >> func acc x >>= \acc' -> bFoldV f func acc' (BList Fz xs)
bFoldV _ _ acc _ = pure acc

-- ============================================================================
-- 2. ARCHITEKTURA GŁĘBOKA
-- ============================================================================

data Synapse = Synapse { conductance :: !FinProb }
data Neuron = Neuron { synapses :: !(BList Synapse), threshold :: !Fin }
data Layer = Layer { neurons :: !(BList Neuron) }
data Network = Network { hiddenLayer :: !Layer, outputLayer :: !Layer } -- 2-Layer Perceptron

-- TRANSMISJA
transmit fuel input (Synapse (FinProb num den)) = do
    tick
    -- Uproszczona hydraulika: próg otwarcia
    halfDen <- subV fuel den (Fs (Fs (Fs (Fs (Fs Fz))))) -- den - 5
    isOpen <- gtV fuel num halfDen
    case isOpen of
        BTrue -> pure (input, Fz)
        _     -> pure (Fz, Fs Fz) -- Opór

-- AKTYWACJA NEURONU
activateNeuron fuel neuron inputs = do
    pairs <- bZip fuel inputs (synapses neuron)
    results <- bMapV fuel (\(i, s) -> transmit fuel i s) pairs
    -- Sumowanie sygnałów
    let BList _ resList = results
    let signals = map fst resList -- Uproszczenie: lista haksellowa wewnatrz blist
    totalSignal <- foldM (\acc x -> tick >> case x of Fz -> pure acc; _ -> succV acc) Fz signals
    -- Próg
    isFire <- gtV fuel totalSignal (threshold neuron)
    let out = case isFire of BTrue -> Fs Fz; _ -> Fz
    pure (out, signals) -- Zwracamy też sygnały wejściowe (potrzebne do uczenia)

-- AKTYWACJA WARSTWY
activateLayer fuel layer inputs = do
    let BList _ ns = neurons layer
    results <- sequence [activateNeuron fuel n inputs | n <- ns]
    let outputs = map fst results
    let debugSigs = map snd results
    pure (BList (Fs (Fs Fz)) outputs, debugSigs) -- Hardcoded cap 2/1

-- FORWARD PASS SIECI
forwardPass fuel net inputs = do
    (hiddenOuts, hSigs) <- activateLayer fuel (hiddenLayer net) inputs
    (finalOuts, fSigs) <- activateLayer fuel (outputLayer net) hiddenOuts
    -- Bierzemy pierwszy output (zakładamy sieć 2-2-1 dla XOR)
    let BList _ (out:_) = finalOuts
    pure (out, hiddenOuts, hSigs, fSigs)

-- ============================================================================
-- 3. UCZENIE GŁĘBOKIE (BACKPRESSURE)
-- ============================================================================

erode fuel (Synapse (FinProb n d)) = do
    tick
    maxN <- subV fuel d (Fs Fz)
    isMax <- gtV fuel n maxN
    case isMax of BTrue -> pure $ Synapse (FinProb n d); _ -> succV n >>= \n' -> pure $ Synapse (FinProb n' d)

constrict fuel (Synapse (FinProb n d)) = do
    tick
    minN <- succV (Fs Fz) -- 2
    isMin <- ltV fuel n minN
    case isMin of BTrue -> pure $ Synapse (FinProb (Fs Fz) d); _ -> predV n >>= \n' -> pure $ Synapse (FinProb n' d)

-- Propagacja błędu dla jednego neuronu
adjustNeuron fuel neuron inputs errorDirection = do
    pairs <- bZip fuel inputs (synapses neuron)
    newSyns <- bMapV fuel (\(inp, syn) -> case inp of
        Fz -> pure syn -- Brak inputu = brak zmiany
        _  -> case errorDirection of
                Undershoot -> erode fuel syn     -- Otwórz rurę
                Overshoot  -> constrict fuel syn -- Przymknij
                Match      -> erode fuel syn     -- Nagródź sukces
        ) pairs
    pure $ neuron { synapses = newSyns }

-- GŁÓWNA FUNKCJA TRENINGOWA
trainNetwork fuel net inputs target = do
    -- 1. Forward
    (output, hiddenOuts, hSigs, fSigs) <- forwardPass fuel net inputs
    
    -- 2. Oblicz błąd wyjściowy
    outIs0 <- eqV fuel output Fz
    targIs0 <- eqV fuel target Fz
    err <- case (outIs0, targIs0) of
        (BTrue, BTrue) -> pure Match
        (BFalse, BFalse) -> pure Match
        (BTrue, BFalse) -> pure Undershoot -- Chcieliśmy 1, jest 0
        (BFalse, BTrue) -> pure Overshoot  -- Chcieliśmy 0, jest 1
        
    -- 3. Backpressure -> Output Layer
    -- Bierzemy jedyny neuron wyjściowy
    let BList _ [outNeuron] = neurons (outputLayer net)
    newOutNeuron <- adjustNeuron fuel outNeuron hiddenOuts err
    let newOutputLayer = Layer (BList (Fs Fz) [newOutNeuron])
    
    -- 4. Backpressure -> Hidden Layer
    -- To jest "Trick VOID": Propagujemy błąd tylko do tych neuronów ukrytych,
    -- które były aktywne (lub powinny być).
    -- Jeśli Output=Undershoot (za mało), to winne są te ukryte, które dały 0 (a mogły dać 1) LUB te co dały 1 (ale słabo).
    -- UPROSZCZENIE: Propagujemy ten sam rodzaj błędu głębiej.
    
    let BList _ hNeurons = neurons (hiddenLayer net)
    -- Zipujemy neurony z ich oryginalnymi wejściami
    newHNeurons <- sequence [ adjustNeuron fuel n inputs err | n <- hNeurons ]
    
    let newHiddenLayer = Layer (BList (Fs (Fs Fz)) newHNeurons)
    let newNet = Network newHiddenLayer newOutputLayer
    
    pure (newNet, output, err)


-- ============================================================================
-- 4. HELPERY BOUNDARY
-- ============================================================================
finToI :: Fin -> Int
finToI = go 20000 where go 0 _ = -1; go _ Fz = 0; go l (Fs n) = 1 + go (l-1) n

fin10k = foldr ($) Fz (replicate 10000 Fs) -- Budżet 10k
fin5k  = foldr ($) Fz (replicate 5000 Fs) 
fin20  = foldr ($) Fz (replicate 20 Fs)
fin10  = foldr ($) Fz (replicate 10 Fs)
fin5   = foldr ($) Fz (replicate 5 Fs)
fin3   = foldr ($) Fz (replicate 3 Fs)
fin2   = foldr ($) Fz (replicate 2 Fs)
fin1   = Fs Fz; fin0 = Fz

-- ============================================================================
-- 5. MAIN
-- ============================================================================
main :: IO ()
main = do
    putStrLn "=== VOID DEEP NETWORK: XOR GATE ==="
    putStrLn "Architecture: 2 Inputs -> 2 Hidden -> 1 Output"
    putStrLn "Budget: 10,000 Ticks (This will be tight...)"
    
    let budget = fin10k
    let fuel   = fin5k -- Duży limit dla rekurencji
    let w      = World budget Fz
    
    -- Init: Wąskie rury (3/10)
    let synInit = Synapse (FinProb fin3 fin10)
    -- Hidden Layer: 2 neurony, każdy ma 2 wejścia
    let hN1 = Neuron (BList fin2 [synInit, synInit]) fin1
    let hN2 = Neuron (BList fin2 [synInit, synInit]) fin1 -- Asymetria by się przydała, ale startujemy symetrycznie
    let hLayer = Layer (BList fin2 [hN1, hN2])
    
    -- Output Layer: 1 neuron, ma 2 wejścia (od Hidden)
    let oN1 = Neuron (BList fin2 [synInit, synInit]) fin1
    let oLayer = Layer (BList fin1 [oN1])
    
    let net = Network hLayer oLayer
    
    -- XOR Dataset
    let ds = [ (BList fin2 [fin0, fin0], fin0)
             , (BList fin2 [fin0, fin1], fin1)
             , (BList fin2 [fin1, fin0], fin1)
             , (BList fin2 [fin1, fin1], fin0) 
             ]
             
    -- Pętla treningowa
    let trainLoop epochCounter currentNet currentWorld = do
            case epochCounter of
                Fz -> putStrLn "Limit epok."
                Fs rest -> do
                    putStrLn $ "Epochs left: " ++ show (finToI rest)
                    let runDS [] n w sc = pure (n, w, sc)
                        runDS ((i,t):xs) n w sc = do
                            let (res, w') = runVoid (trainNetwork fuel n i t) w
                            case res of
                                Nothing -> error "SYSTEM DIED (Computational Limit Reached)"
                                Just (n', out, err) -> do
                                    let isOk = out == t
                                    let mark = if isOk then "v" else "x"
                                    -- putStrLn $ "  Out: " ++ show (finToI out) ++ " " ++ mark
                                    let newSc = if isOk then (Fs sc) else sc
                                    runDS xs n' w' newSc
                                    
                    (nextNet, nextWorld, score) <- runDS ds currentNet currentWorld Fz
                    putStrLn $ "  Score: " ++ show (finToI score) ++ "/4 | Heat: " ++ show (finToI (wHeat nextWorld))
                    
                    if (finToI score) == 4 
                        then putStrLn ">>> XOR SOLVED! <<<"
                        else trainLoop rest nextNet nextWorld

    -- START
    trainLoop fin20 net w