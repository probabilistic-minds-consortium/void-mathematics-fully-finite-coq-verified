-- void_astro_pure.hs - VOID ASTROLOGY: Pure Finite Celestial Mechanics
-- Every operation pays. No infinity. No cheating.
-- "The stars incline, but do not compel. And even inclination costs."

module Main where

-- ============================================================================
-- 1. ONTOLOGIA - TYLKO Fin, ŻADNYCH Int W LOGICE
-- ============================================================================

data Fin = Fz | Fs !Fin deriving (Eq, Ord)

instance Show Fin where
    show = go 5000
      where
        go 0 _ = "..."
        go _ Fz = "0"
        go limit (Fs n) = show (1 + countFin (limit - 1) n)
        
        countFin 0 _ = 0
        countFin _ Fz = 0
        countFin limit (Fs n) = 1 + countFin (limit - 1) n

-- Trójwartościowa logika
data Bool3 = BTrue | BFalse | BUnknown deriving (Show, Eq)

-- ============================================================================
-- 2. TERMODYNAMIKA
-- ============================================================================

data World = World
    { wBudget :: !Fin
    , wHeat   :: !Fin
    } deriving (Show)

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

-- Jedyny sposób na zmianę świata
tick :: Void ()
tick = Void $ \w -> case wBudget w of
    Fz -> (Nothing, w)
    Fs b' -> (Just (), w { wBudget = b', wHeat = Fs (wHeat w) })

-- ============================================================================
-- 3. ARYTMETYKA PŁATNA - KAŻDA OPERACJA KOSZTUJE
-- ============================================================================

-- Porównanie mniejszości - płatne, z fuel
ltV :: Fin -> Fin -> Fin -> Void Bool3
ltV Fz _ _ = pure BUnknown
ltV _ Fz (Fs _) = tick >> pure BTrue
ltV _ Fz Fz = tick >> pure BFalse
ltV _ (Fs _) Fz = tick >> pure BFalse
ltV (Fs fuel) (Fs a) (Fs b) = tick >> ltV fuel a b

-- Równość - płatna, z fuel
eqV :: Fin -> Fin -> Fin -> Void Bool3
eqV Fz _ _ = pure BUnknown
eqV _ Fz Fz = tick >> pure BTrue
eqV _ Fz (Fs _) = tick >> pure BFalse
eqV _ (Fs _) Fz = tick >> pure BFalse
eqV (Fs fuel) (Fs a) (Fs b) = tick >> eqV fuel a b

-- Dodawanie - płatne, O(m)
addV :: Fin -> Fin -> Fin -> Void Fin
addV Fz _ _ = pure Fz
addV _ a Fz = pure a
addV (Fs fuel) a (Fs b) = tick >> addV fuel (Fs a) b

-- Odejmowanie (saturowane do Fz) - płatne, O(min(a,b))
subV :: Fin -> Fin -> Fin -> Void Fin
subV Fz _ _ = pure Fz
subV _ a Fz = pure a
subV _ Fz _ = pure Fz
subV (Fs fuel) (Fs a) (Fs b) = tick >> subV fuel a b

-- Mnożenie - płatne, O(n*m) zgodnie z VOID
mulV :: Fin -> Fin -> Fin -> Void Fin
mulV Fz _ _ = pure Fz
mulV _ _ Fz = pure Fz
mulV _ Fz _ = pure Fz
mulV (Fs fuel) a (Fs b) = do
    tick
    rest <- mulV fuel a b
    addV fuel a rest

-- Modulo - płatne, przez powtórne odejmowanie
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

-- Dzielenie całkowite - płatne
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
-- 4. STRUKTURY OGRANICZONE
-- ============================================================================

-- Mapuj z fuel - PŁATNE
mapV :: Fin -> (a -> Void b) -> [a] -> Void [b]
mapV Fz _ _ = pure []
mapV _ _ [] = pure []
mapV (Fs fuel) f (x:xs) = do
    tick
    y <- f x
    ys <- mapV fuel f xs
    pure (y : ys)

-- ============================================================================
-- 5. STAŁE JAKO Fin
-- ============================================================================

fin0, fin1, fin2, fin3, fin4, fin5 :: Fin
fin0 = Fz
fin1 = Fs fin0
fin2 = Fs fin1
fin3 = Fs fin2
fin4 = Fs fin3
fin5 = Fs fin4

fin6, fin7, fin8, fin9, fin10, fin11, fin12 :: Fin
fin6 = Fs fin5
fin7 = Fs fin6
fin8 = Fs fin7
fin9 = Fs fin8
fin10 = Fs fin9
fin11 = Fs fin10
fin12 = Fs fin11

-- Darmowe dodawanie TYLKO dla stałych (compile-time)
addPure :: Fin -> Fin -> Fin
addPure a Fz = a
addPure a (Fs b) = Fs (addPure a b)

fin30 :: Fin
fin30 = addPure fin10 (addPure fin10 fin10)

fin60 :: Fin
fin60 = addPure fin30 fin30

fin90 :: Fin
fin90 = addPure fin60 fin30

fin120 :: Fin
fin120 = addPure fin60 fin60

fin180 :: Fin
fin180 = addPure fin90 fin90

fin360 :: Fin
fin360 = addPure fin180 fin180

fin500 :: Fin
fin500 = addPure (addPure fin180 fin180) (addPure fin90 (addPure fin30 fin10))

fin1000 :: Fin
fin1000 = addPure fin500 fin500

fin2000 :: Fin
fin2000 = addPure fin1000 fin1000

fin5000 :: Fin
fin5000 = addPure fin2000 (addPure fin2000 fin1000)

fin10000 :: Fin
fin10000 = addPure fin5000 fin5000

-- ============================================================================
-- 6. ZODIAK - 12 ZNAKÓW JAKO Fin
-- ============================================================================

data Sign = Sign !Fin deriving (Eq)

instance Show Sign where
    show (Sign n) = signName n
      where
        signName s
            | s == fin0 = "Aries"
            | s == fin1 = "Taurus"
            | s == fin2 = "Gemini"
            | s == fin3 = "Cancer"
            | s == fin4 = "Leo"
            | s == fin5 = "Virgo"
            | s == fin6 = "Libra"
            | s == fin7 = "Scorpio"
            | s == fin8 = "Sagittarius"
            | s == fin9 = "Capricorn"
            | s == fin10 = "Aquarius"
            | s == fin11 = "Pisces"
            | otherwise = "?"

-- Stopnie (0-359) na znak (0-11)
degreeToSign :: Fin -> Fin -> Void Sign
degreeToSign fuel deg = do
    tick
    signNum <- divV fuel deg fin30
    m <- modV fuel signNum fin12
    pure (Sign m)

-- ============================================================================
-- 7. PLANETY
-- ============================================================================

data Planet = Planet !Fin deriving (Eq)

instance Show Planet where
    show (Planet n)
        | n == fin0 = "Sun"
        | n == fin1 = "Moon"
        | n == fin2 = "Mercury"
        | otherwise = "Planet" ++ show n

-- Pozycje startowe
planetStart :: Planet -> Fin
planetStart (Planet n)
    | n == fin0 = fin0              -- Sun at 0°
    | n == fin1 = fin60             -- Moon at 60°
    | n == fin2 = fin30             -- Mercury at 30°
    | otherwise = fin90

-- Prędkość (stopni na tick czasu) - NISKA żeby oszczędzić budżet
planetSpeed :: Planet -> Fin
planetSpeed (Planet n)
    | n == fin0 = fin1              -- Sun: 1°/day
    | n == fin1 = fin2              -- Moon: 2°/day (uproszczone!)
    | n == fin2 = fin1              -- Mercury: 1°/day
    | otherwise = fin0

-- ============================================================================
-- 8. POZYCJA PLANETY
-- ============================================================================

data PlanetPos = PlanetPos
    { ppPlanet :: !Planet
    , ppDegree :: !Fin
    , ppSign   :: !Sign
    } deriving (Show)

-- Oblicz pozycję - PŁATNE
calcPosition :: Fin -> Planet -> Fin -> Void PlanetPos
calcPosition fuel planet time = do
    tick
    let start = planetStart planet
    let speed = planetSpeed planet
    moved <- mulV fuel time speed
    total <- addV fuel start moved
    deg <- modV fuel total fin360
    sign <- degreeToSign fuel deg
    pure PlanetPos
        { ppPlanet = planet
        , ppDegree = deg
        , ppSign = sign
        }

-- ============================================================================
-- 9. ASPEKTY
-- ============================================================================

data AspectType = Conjunction | Sextile | Square | Trine | Opposition | NoAspect
                deriving (Show, Eq)

data Aspect = Aspect
    { aPlanet1 :: !Planet
    , aPlanet2 :: !Planet
    , aType    :: !AspectType
    } deriving (Show)

-- Różnica kątowa
angleDiff :: Fin -> Fin -> Fin -> Void Fin
angleDiff fuel a b = do
    tick
    greater <- ltV fuel b a
    case greater of
        BTrue -> subV fuel a b
        _ -> subV fuel b a

-- Klasyfikuj aspekt - uproszczone
classifyAspect :: Fin -> Fin -> Void AspectType
classifyAspect fuel diff = do
    tick
    -- Koniunkcja: diff < 10
    isSmall <- ltV fuel diff fin10
    case isSmall of
        BTrue -> pure Conjunction
        _ -> do
            -- Square: 80-100 (około 90)
            is80 <- ltV fuel (addPure fin60 (addPure fin10 fin10)) diff
            is100 <- ltV fuel diff (addPure fin90 fin10)
            case (is80, is100) of
                (BTrue, BTrue) -> pure Square
                _ -> do
                    -- Trine: 110-130 (około 120)
                    is110 <- ltV fuel (addPure fin90 (addPure fin10 fin10)) diff
                    is130 <- ltV fuel diff (addPure fin120 fin10)
                    case (is110, is130) of
                        (BTrue, BTrue) -> pure Trine
                        _ -> pure NoAspect

-- Wykryj aspekt
detectAspect :: Fin -> PlanetPos -> PlanetPos -> Void (Maybe Aspect)
detectAspect fuel p1 p2 = do
    tick
    diff <- angleDiff fuel (ppDegree p1) (ppDegree p2)
    aspType <- classifyAspect fuel diff
    case aspType of
        NoAspect -> pure Nothing
        _ -> pure $ Just Aspect
            { aPlanet1 = ppPlanet p1
            , aPlanet2 = ppPlanet p2
            , aType = aspType
            }

-- ============================================================================
-- 10. HOROSKOP
-- ============================================================================

data Horoscope = Horoscope
    { hPositions :: ![PlanetPos]
    , hAspects   :: ![Aspect]
    } deriving (Show)

-- Tylko 3 planety - oszczędność budżetu
allPlanets :: [Planet]
allPlanets = [Planet fin0, Planet fin1, Planet fin2]

-- Rzuć horoskop
castHoroscope :: Fin -> Fin -> Void Horoscope
castHoroscope fuel time = do
    tick
    
    -- Oblicz pozycje
    positions <- mapV fuel (\p -> calcPosition fuel p time) allPlanets
    
    -- Znajdź aspekty
    aspects <- findAspects fuel positions
    
    pure Horoscope
        { hPositions = positions
        , hAspects = aspects
        }

-- Znajdź aspekty - tylko między sąsiednimi (O(n) nie O(n²))
findAspects :: Fin -> [PlanetPos] -> Void [Aspect]
findAspects _ [] = pure []
findAspects _ [_] = pure []
findAspects fuel (p1:p2:rest) = do
    tick
    maybeAsp <- detectAspect fuel p1 p2
    restAsp <- findAspects fuel (p2:rest)
    case maybeAsp of
        Nothing -> pure restAsp
        Just a -> pure (a : restAsp)

-- ============================================================================
-- 11. WIZUALIZACJA
-- ============================================================================

renderHoroscope :: Horoscope -> String
renderHoroscope h = unlines $
    [ ""
    , "=== CELESTIAL MAP ==="
    , ""
    , "POSITIONS:"
    ] ++
    [renderPos p | p <- hPositions h] ++
    [ ""
    , "ASPECTS:"
    ] ++
    (if null (hAspects h) 
     then ["  (no major aspects)"]
     else [renderAsp a | a <- hAspects h])

renderPos :: PlanetPos -> String
renderPos p = 
    "  " ++ padRight 10 (show (ppPlanet p)) ++ 
    padRight 5 (show (ppDegree p)) ++ "° " ++ 
    show (ppSign p)

renderAsp :: Aspect -> String
renderAsp a =
    "  " ++ show (aPlanet1 a) ++ " " ++ 
    aspSymbol (aType a) ++ " " ++ show (aPlanet2 a)

aspSymbol :: AspectType -> String
aspSymbol Conjunction = "☌"
aspSymbol Sextile = "⚹"
aspSymbol Square = "□"
aspSymbol Trine = "△"
aspSymbol Opposition = "☍"
aspSymbol NoAspect = "-"

padRight :: Int -> String -> String
padRight n s = s ++ replicate (max 0 (n - length s)) ' '

-- ============================================================================
-- 12. MAIN
-- ============================================================================

main :: IO ()
main = do
    putStrLn "╔════════════════════════════════════════════════════╗"
    putStrLn "║     VOID ASTROLOGY: Pure Finite Mechanics          ║"
    putStrLn "║                                                    ║"
    putStrLn "║  'The stars incline, but do not compel.           ║"
    putStrLn "║   And even inclination costs.'                    ║"
    putStrLn "╚════════════════════════════════════════════════════╝"
    putStrLn ""
    
    let budget = fin10000
    let time = fin3          -- 3 dni od epoki
    let fuel = fin1000
    
    let world = World budget Fz
    
    putStrLn $ "Budget: " ++ show budget
    putStrLn $ "Time: Day " ++ show time
    putStrLn $ "Planets: Sun, Moon, Mercury"
    putStrLn ""
    
    putStrLn "Casting horoscope..."
    let (result, world') = runVoid (castHoroscope fuel time) world
    
    case result of
        Nothing -> do
            putStrLn ""
            putStrLn "════════════════════════════════════════"
            putStrLn "BUDGET EXHAUSTED - The stars went dark."
            putStrLn $ "Heat generated: " ++ show (wHeat world')
        Just horoscope -> do
            putStrLn $ renderHoroscope horoscope
            putStrLn "════════════════════════════════════════"
            putStrLn $ "Budget remaining: " ++ show (wBudget world')
            putStrLn $ "Heat generated: " ++ show (wHeat world')
            putStrLn ""
            putStrLn "The stars have spoken. The cost has been paid."