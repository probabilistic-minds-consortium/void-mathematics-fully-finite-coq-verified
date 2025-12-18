-- void_astro_pure.hs - VOID ASTROLOGY
-- All results are uncertainties in (0,1). No exact values exist.

module Main where

-- ============================================================================
-- 1. ONTOLOGY
-- ============================================================================

data Fin = Fz | Fs !Fin deriving (Eq, Ord)

-- FinProb: (numerator, denominator) representing value in (0,1)
-- NEVER exactly 0 or 1
data FinProb = FinProb !Fin !Fin deriving (Eq)

data Bool3 = BTrue | BFalse | BUnknown deriving (Eq)

-- ============================================================================
-- 2. BOUNDED STRUCTURES
-- ============================================================================

data BList a = BList !Fin ![a]

bEmpty :: Fin -> BList a
bEmpty cap = BList cap []

-- ============================================================================
-- 3. THERMODYNAMICS
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
    Void x >>= f = Void $ \w -> case x w of
        (Just v, w') -> runVoid (f v) w'
        (Nothing, w') -> (Nothing, w')

tick :: Void ()
tick = Void $ \w -> case wBudget w of
    Fz -> (Nothing, w)
    Fs b' -> (Just (), w { wBudget = b', wHeat = Fs (wHeat w) })

-- ============================================================================
-- 4. PAID ARITHMETIC
-- ============================================================================

ltV :: Fin -> Fin -> Fin -> Void Bool3
ltV Fz _ _ = pure BUnknown
ltV _ Fz (Fs _) = tick >> pure BTrue
ltV _ Fz Fz = tick >> pure BFalse
ltV _ (Fs _) Fz = tick >> pure BFalse
ltV (Fs fuel) (Fs a) (Fs b) = tick >> ltV fuel a b

addV :: Fin -> Fin -> Fin -> Void Fin
addV Fz _ _ = pure Fz
addV _ a Fz = pure a
addV (Fs fuel) a (Fs b) = tick >> addV fuel (Fs a) b

subV :: Fin -> Fin -> Fin -> Void Fin
subV Fz _ _ = pure Fz
subV _ a Fz = pure a
subV _ Fz _ = pure Fz
subV (Fs fuel) (Fs a) (Fs b) = tick >> subV fuel a b

mulV :: Fin -> Fin -> Fin -> Void Fin
mulV Fz _ _ = pure Fz
mulV _ _ Fz = pure Fz
mulV _ Fz _ = pure Fz
mulV (Fs fuel) a (Fs b) = do
    tick
    rest <- mulV fuel a b
    addV fuel a rest

modV :: Fin -> Fin -> Fin -> Void Fin
modV Fz _ _ = pure Fz
modV _ a Fz = pure Fz
modV (Fs fuel) a b = do
    tick
    less <- ltV fuel a b
    case less of
        BTrue -> pure a
        BUnknown -> pure a
        BFalse -> do
            diff <- subV fuel a b
            modV fuel diff b

divV :: Fin -> Fin -> Fin -> Void Fin
divV Fz _ _ = pure Fz
divV _ _ Fz = pure Fz
divV fuel a b = divLoop fuel a b Fz
  where
    divLoop Fz _ _ acc = pure acc
    divLoop (Fs f) x y acc = do
        tick
        less <- ltV f x y
        case less of
            BTrue -> pure acc
            BUnknown -> pure acc
            BFalse -> do
                diff <- subV f x y
                divLoop f diff y (Fs acc)

-- ============================================================================
-- 5. FinProb OPERATIONS (all in (0,1))
-- ============================================================================

-- Ensure value stays in open interval (0,1)
-- If numerator = 0, set to 1 (minimal positive)
-- If numerator >= denominator, set to denominator - 1
clampToOpen :: Fin -> Fin -> Fin -> Void FinProb
clampToOpen fuel num denom = do
    tick
    case num of
        Fz -> pure (FinProb (Fs Fz) denom)  -- 0 -> 1/denom (near zero but not zero)
        _ -> do
            geq <- ltV fuel num denom
            case geq of
                BFalse -> do  -- num >= denom, clamp to (denom-1)/denom
                    clamped <- subV fuel denom (Fs Fz)
                    pure (FinProb clamped denom)
                _ -> pure (FinProb num denom)

-- Create FinProb from position in cycle (e.g., degree in 360)
-- Returns fraction of full cycle with uncertainty
positionToProb :: Fin -> Fin -> Fin -> Void FinProb
positionToProb fuel pos fullCycle = do
    tick
    m <- modV fuel pos fullCycle
    -- Add 1 to both to ensure (0,1): (m+1)/(fullCycle+2)
    num <- addV fuel m (Fs Fz)
    denom <- addV fuel fullCycle (Fs (Fs Fz))
    clampToOpen fuel num denom

-- Confidence decreases with heat (more computation = more uncertainty)
-- confidence = 1 - (heat / maxHeat) clamped to (0,1)
computeConfidence :: Fin -> Fin -> Fin -> Void FinProb
computeConfidence fuel heat maxHeat = do
    tick
    -- confidence numerator = maxHeat - heat (but at least 1)
    diff <- subV fuel maxHeat heat
    case diff of
        Fz -> pure (FinProb (Fs Fz) maxHeat)  -- minimal confidence
        _ -> clampToOpen fuel diff maxHeat

-- ============================================================================
-- 6. BOUNDED LIST OPERATIONS
-- ============================================================================

bMapV :: Fin -> (a -> Void b) -> BList a -> Void (BList b)
bMapV fuel f (BList cap items) = do
    mapped <- bMapList fuel f items
    pure (BList cap mapped)
  where
    bMapList Fz _ _ = pure []
    bMapList _ _ [] = pure []
    bMapList (Fs fu) g (x:xs) = do
        tick
        y <- g x
        ys <- bMapList fu g xs
        pure (y : ys)

-- ============================================================================
-- 7. CONSTANTS AS Fin
-- ============================================================================

fin0, fin1, fin2, fin3, fin4, fin5, fin6, fin7, fin8, fin9, fin10, fin11, fin12 :: Fin
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
fin11 = Fs fin10
fin12 = Fs fin11

addPure :: Fin -> Fin -> Fin
addPure a Fz = a
addPure a (Fs b) = Fs (addPure a b)

fin30, fin60, fin90, fin120, fin180, fin360 :: Fin
fin30 = addPure fin10 (addPure fin10 fin10)
fin60 = addPure fin30 fin30
fin90 = addPure fin60 fin30
fin120 = addPure fin60 fin60
fin180 = addPure fin90 fin90
fin360 = addPure fin180 fin180

fin500, fin1000, fin2000, fin5000, fin10000 :: Fin
fin500 = addPure (addPure fin180 fin180) (addPure fin90 (addPure fin30 fin10))
fin1000 = addPure fin500 fin500
fin2000 = addPure fin1000 fin1000
fin5000 = addPure fin2000 (addPure fin2000 fin1000)
fin10000 = addPure fin5000 fin5000

-- ============================================================================
-- 8. ZODIAC AS FinProb
-- ============================================================================

-- Sign is NOT a discrete value but a FinProb indicating
-- probability mass in that region of the zodiac
data SignProb = SignProb
    { spIndex      :: !Fin      -- which sign (0-11)
    , spStrength   :: !FinProb  -- how strongly in this sign (0,1)
    }

-- Degree to sign with uncertainty
degreeToSignProb :: Fin -> Fin -> Void SignProb
degreeToSignProb fuel deg = do
    tick
    signNum <- divV fuel deg fin30
    m <- modV fuel signNum fin12
    -- Position within sign as fraction
    posInSign <- modV fuel deg fin30
    strength <- positionToProb fuel posInSign fin30
    pure SignProb
        { spIndex = m
        , spStrength = strength
        }

-- ============================================================================
-- 9. PLANETS
-- ============================================================================

newtype Planet = Planet Fin deriving (Eq)

planetStart :: Planet -> Fin
planetStart (Planet p) = case p of
    Fz -> fin0
    Fs Fz -> fin60
    Fs (Fs Fz) -> fin30
    _ -> fin90

planetSpeed :: Planet -> Fin
planetSpeed (Planet p) = case p of
    Fz -> fin1
    Fs Fz -> fin2
    Fs (Fs Fz) -> fin1
    _ -> Fz

-- ============================================================================
-- 10. HOROSCOPE WITH UNCERTAINTIES
-- ============================================================================

-- Planet position is NOT exact but a probability distribution
data PlanetPos = PlanetPos
    { ppPlanet     :: !Planet
    , ppPosition   :: !FinProb   -- position as fraction of full circle (0,1)
    , ppSign       :: !SignProb  -- sign with strength
    , ppConfidence :: !FinProb   -- confidence decreases with computation
    }

-- Aspect strength is a FinProb, not binary
data Aspect = Aspect
    { aPlanet1  :: !Planet
    , aPlanet2  :: !Planet
    , aOrbProb  :: !FinProb  -- how close to exact aspect (higher = closer)
    , aHarmony  :: !Bool3    -- harmonious/tense/unknown
    }

data Horoscope = Horoscope
    { hPositions   :: !(BList PlanetPos)
    , hAspects     :: !(BList Aspect)
    , hConfidence  :: !FinProb  -- overall chart confidence
    }

-- Calculate position with uncertainty
calcPosition :: Fin -> Fin -> Planet -> Fin -> Void PlanetPos
calcPosition fuel maxHeat planet time = do
    tick
    let start = planetStart planet
    let speed = planetSpeed planet
    moved <- mulV fuel time speed
    total <- addV fuel start moved
    deg <- modV fuel total fin360
    
    -- Position as FinProb
    posProb <- positionToProb fuel deg fin360
    
    -- Sign with uncertainty
    signProb <- degreeToSignProb fuel deg
    
    -- Confidence based on heat accumulated
    currentHeat <- Void $ \w -> (Just (wHeat w), w)
    conf <- computeConfidence fuel currentHeat maxHeat
    
    pure PlanetPos
        { ppPlanet = planet
        , ppPosition = posProb
        , ppSign = signProb
        , ppConfidence = conf
        }

-- Aspect detection returns strength as FinProb
detectAspect :: Fin -> Fin -> PlanetPos -> PlanetPos -> Void (Maybe Aspect)
detectAspect fuel maxHeat p1 p2 = do
    tick
    let FinProb n1 d1 = ppPosition p1
    let FinProb n2 d2 = ppPosition p2
    
    -- Compute angular difference (simplified)
    diff <- if n1 > n2 
            then subV fuel n1 n2
            else subV fuel n2 n1
    
    -- Check proximity to major aspects (0, 90, 120, 180 degrees = 0, 1/4, 1/3, 1/2)
    -- Orb tolerance as FinProb
    
    -- Conjunction: diff near 0 (or near full circle)
    isNearZero <- ltV fuel diff fin10
    case isNearZero of
        BTrue -> do
            -- Strong conjunction - orb is (10-diff)/10
            orbNum <- subV fuel fin10 diff
            orbProb <- clampToOpen fuel orbNum fin10
            pure $ Just Aspect
                { aPlanet1 = ppPlanet p1
                , aPlanet2 = ppPlanet p2
                , aOrbProb = orbProb
                , aHarmony = BUnknown  -- conjunction is neutral
                }
        _ -> do
            -- Check square (near 90/360 = 1/4)
            let quarterCircle = fin90
            diffFrom90 <- if diff > quarterCircle
                          then subV fuel diff quarterCircle
                          else subV fuel quarterCircle diff
            isNear90 <- ltV fuel diffFrom90 fin10
            case isNear90 of
                BTrue -> do
                    orbNum <- subV fuel fin10 diffFrom90
                    orbProb <- clampToOpen fuel orbNum fin10
                    pure $ Just Aspect
                        { aPlanet1 = ppPlanet p1
                        , aPlanet2 = ppPlanet p2
                        , aOrbProb = orbProb
                        , aHarmony = BFalse  -- square is tense
                        }
                _ -> do
                    -- Check trine (near 120/360 = 1/3)
                    diffFrom120 <- if diff > fin120
                                   then subV fuel diff fin120
                                   else subV fuel fin120 diff
                    isNear120 <- ltV fuel diffFrom120 fin10
                    case isNear120 of
                        BTrue -> do
                            orbNum <- subV fuel fin10 diffFrom120
                            orbProb <- clampToOpen fuel orbNum fin10
                            pure $ Just Aspect
                                { aPlanet1 = ppPlanet p1
                                , aPlanet2 = ppPlanet p2
                                , aOrbProb = orbProb
                                , aHarmony = BTrue  -- trine is harmonious
                                }
                        _ -> pure Nothing

allPlanets :: BList Planet
allPlanets = BList fin3 [Planet fin0, Planet fin1, Planet fin2]

findAspects :: Fin -> Fin -> [PlanetPos] -> BList Aspect -> Void (BList Aspect)
findAspects _ _ [] acc = pure acc
findAspects _ _ [_] acc = pure acc
findAspects Fz _ _ acc = pure acc
findAspects (Fs fuel) maxHeat (p1:p2:rest) (BList cap items) = do
    tick
    maybeAsp <- detectAspect fuel maxHeat p1 p2
    newItems <- case maybeAsp of
        Nothing -> pure items
        Just a -> pure (a : items)
    findAspects fuel maxHeat (p2:rest) (BList cap newItems)

castHoroscope :: Fin -> Fin -> Fin -> Void Horoscope
castHoroscope fuel maxHeat time = do
    tick
    positions <- bMapV fuel (\p -> calcPosition fuel maxHeat p time) allPlanets
    let BList _ posList = positions
    aspects <- findAspects fuel maxHeat posList (bEmpty fin10)
    
    -- Overall confidence
    finalHeat <- Void $ \w -> (Just (wHeat w), w)
    overallConf <- computeConfidence fuel finalHeat maxHeat
    
    pure Horoscope
        { hPositions = positions
        , hAspects = aspects
        , hConfidence = overallConf
        }

-- ============================================================================
-- PART II: BOUNDARY
-- ============================================================================

boundary_finToInt :: Fin -> Int
boundary_finToInt = go 10000
  where
    go 0 _ = -1
    go _ Fz = 0
    go limit (Fs n) = 1 + go (limit - 1) n

boundary_finProbToString :: FinProb -> String
boundary_finProbToString (FinProb n d) =
    show (boundary_finToInt n) ++ "/" ++ show (boundary_finToInt d)

boundary_signName :: Fin -> String
boundary_signName n = case boundary_finToInt n of
    0 -> "Aries"; 1 -> "Taurus"; 2 -> "Gemini"; 3 -> "Cancer"
    4 -> "Leo"; 5 -> "Virgo"; 6 -> "Libra"; 7 -> "Scorpio"
    8 -> "Sagittarius"; 9 -> "Capricorn"; 10 -> "Aquarius"; 11 -> "Pisces"
    _ -> "?"

boundary_planetName :: Planet -> String
boundary_planetName (Planet n) = case boundary_finToInt n of
    0 -> "Sun"; 1 -> "Moon"; 2 -> "Mercury"
    _ -> "Planet"

boundary_harmonyName :: Bool3 -> String
boundary_harmonyName BTrue = "harmonious"
boundary_harmonyName BFalse = "tense"
boundary_harmonyName BUnknown = "neutral"

boundary_renderPosition :: PlanetPos -> String
boundary_renderPosition p =
    "  " ++ boundary_planetName (ppPlanet p) ++ ":\n" ++
    "    position: " ++ boundary_finProbToString (ppPosition p) ++ " of circle\n" ++
    "    sign: " ++ boundary_signName (spIndex (ppSign p)) ++ 
    " (strength: " ++ boundary_finProbToString (spStrength (ppSign p)) ++ ")\n" ++
    "    confidence: " ++ boundary_finProbToString (ppConfidence p)

boundary_renderAspect :: Aspect -> String
boundary_renderAspect a =
    "  " ++ boundary_planetName (aPlanet1 a) ++ " - " ++
    boundary_planetName (aPlanet2 a) ++ ":\n" ++
    "    orb strength: " ++ boundary_finProbToString (aOrbProb a) ++ "\n" ++
    "    quality: " ++ boundary_harmonyName (aHarmony a)

boundary_renderHoroscope :: Horoscope -> String
boundary_renderHoroscope h =
    let BList _ positions = hPositions h
        BList _ aspects = hAspects h
    in unlines $
        [ "", "=== CELESTIAL MAP ===" 
        , ""
        , "Overall confidence: " ++ boundary_finProbToString (hConfidence h)
        , ""
        , "POSITIONS:"
        ] ++
        map boundary_renderPosition positions ++
        [ "", "ASPECTS:" ] ++
        (if null aspects
         then ["  (no major aspects detected within orb tolerance)"]
         else map boundary_renderAspect aspects)

-- ============================================================================
-- MAIN
-- ============================================================================

main :: IO ()
main = do
    putStrLn "========================================================"
    putStrLn "     VOID ASTROLOGY: Pure Finite Mechanics"
    putStrLn ""
    putStrLn "  All values are uncertainties in (0,1)."
    putStrLn "  Nothing is exact. Everything costs."
    putStrLn "========================================================"
    putStrLn ""
    
    let budget = fin10000
    let maxHeat = fin2000  -- for confidence calculation
    let time = fin3
    let fuel = fin1000
    
    let world = World budget Fz
    
    putStrLn $ "Budget: " ++ show (boundary_finToInt budget)
    putStrLn $ "Time: Day " ++ show (boundary_finToInt time)
    putStrLn $ "Planets: Sun, Moon, Mercury"
    putStrLn ""
    
    putStrLn "Casting horoscope..."
    let (result, world') = runVoid (castHoroscope fuel maxHeat time) world
    
    case result of
        Nothing -> do
            putStrLn ""
            putStrLn "========================================"
            putStrLn "BUDGET EXHAUSTED - The stars went dark."
            putStrLn $ "Heat generated: " ++ show (boundary_finToInt (wHeat world'))
        Just horoscope -> do
            putStrLn $ boundary_renderHoroscope horoscope
            putStrLn "========================================"
            putStrLn $ "Budget remaining: " ++ show (boundary_finToInt (wBudget world'))
            putStrLn $ "Heat generated: " ++ show (boundary_finToInt (wHeat world'))
            let conserved = boundary_finToInt (wBudget world') + boundary_finToInt (wHeat world')
            putStrLn $ "Conservation: " ++ show conserved ++ " = " ++ show (boundary_finToInt budget)
            putStrLn ""
            putStrLn "The stars have spoken. Uncertainty remains."