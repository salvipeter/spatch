import Data.List (intercalate, (\\))
import Debug.Trace (traceShow)
import Math.Combinatorics.Exact.Binomial (choose)

type Index = [Int]

count :: (a -> Bool) -> [a] -> Int
count p = length . filter p

indices :: Int -> Int -> [Index]
indices 1 d = [[d]]
indices n d = [i:xs | i <- [0..d], xs <- indices (n-1) (d-i)]

pairSums :: [Int] -> [Int]
pairSums xs = map (uncurry (+)) $ zip ys (tail ys)
    where ys = xs ++ [head xs]

isOuter :: Index -> Bool
isOuter xs = any (== d) $ pairSums xs
    where d = sum xs

isInner :: Index -> Bool
isInner xs = not (isOuter xs) && any isOuter (neighbors xs)

isCentral :: Index -> Bool
isCentral xs = not (isOuter xs) && not (isInner xs)

isTripleFrame :: Index -> Bool
isTripleFrame xs = count (>= d-1) sums > 2
    where sums = pairSums xs
          d    = sum xs

outerIndices n d = filter isOuter (indices n d)
innerIndices n d = filter isInner (indices n d)
centralIndices n d = (cp \\ ocp) \\ icp
    where cp  = indices n d
          ocp = filter isOuter cp
          icp = filter isInner cp

numIndices n d = choose (n+d-1) (n-1)
numInnerIndices n d = length (innerIndices n d) -- 2n(d-1)-n
numCentralIndices n d = length (centralIndices n d)
isDependent n d = any isTripleFrame (indices n d)

allInfo n d | isDependent n d = (0,0,0)
            | otherwise       = (numIndices n d,
                                 numInnerIndices n d,
                                 numCentralIndices n d)

rotate :: [Int] -> [[Int]]
rotate a@(x:xs) = a : rotate (xs ++ [x])

neighbors :: Index -> [Index]
neighbors xs = filter (all (>= 0)) ys
    where n     = length xs
          left  = take n $ rotate $ [1,-1] ++ take (n-2) (repeat 0)
          right = take n $ rotate $ [-1,1] ++ take (n-2) (repeat 0)
          ys    = map (zipWith (+) xs) (left ++ right)

type Point   = [Double]
type Polygon = [Point]

-- assumes that the point is inside
triangleRatio :: Polygon -> Int -> Point -> Double
triangleRatio ps i p = (triangleArea p pi pi1) / (triangleArea pi pi1 pi2)
    where pi  = ps !! i
          pi1 = ps !! ((i+1) `mod` n)
          pi2 = ps !! ((i+2) `mod` n)
          n   = length ps

edgeLength :: Point -> Point -> Double
edgeLength a b = sqrt $ sum $ map (** 2) $ zipWith (-) a b

triangleArea :: Point -> Point -> Point -> Double
triangleArea a b c = heron bc ac ab
    where bc = edgeLength b c
          ac = edgeLength a c
          ab = edgeLength a b

heron :: Double -> Double -> Double -> Double
heron a b c = sqrt $ abs $ s * (s - a) * (s - b) * (s - c)
    where s = (a + b + c) / 2

barycentric :: Polygon -> Point -> [Double]
barycentric ps p = map (/ pisum) pis
    where pis   = map pi [0..n-1]
          pi i  = product [triangleRatio ps j p | j <- [0..n-1], j /= i,
                                                  (j + 1) `mod` n /= i]
          pisum = sum pis
          n     = length ps

regularPolygon :: Int -> [Point]
regularPolygon n = [circlePoint (angle i) | i <- [0..n-1]]
    where circlePoint a = [cos a, sin a]
          angle       i = 2 * pi * fromIntegral i / fromIntegral n

fact :: Int -> Int
fact n = product [1..n]

multinomial :: [Int] -> Int
multinomial is = fact (sum is) `div` (product . map fact) is

bernstein :: Index -> [Double] -> Double
bernstein is us = fromIntegral (multinomial is) * product (zipWith (**) us isf)
    where isf = map fromIntegral is

{- example (cubic 5-sided):
>>> bernstein [2,1,0,0,0] $ barycentric (regularPolygon 5) [0.5, 0.3]
0.21979881212453456
-}

-- assumes that the polygon is centered at the origin
samplePoints :: Polygon -> Int -> [Point]
samplePoints ps res = [0,0] : concat [loop i | i <- [1..res-1]]
    where n          = length ps
          alpha i    = fromIntegral i / fromIntegral (res-1)
          beta i j   = fromIntegral i / fromIntegral j
          loop i     = concat [line i (point i j) (point i ((j+1) `mod` n))
                                   | j <- [0..n-1]]
          point i j  = vmul (alpha i) (ps !! j)
          line i a b = [affinComb (beta j i) a b | j <- [1..i]]

triangles :: Int -> Int -> [(Int,Int,Int)]
triangles n res = connectTriangles loops
    where loops    = center : [loop i | i <- [1..res-1]]
          center   = take n $ repeat [0]
          loop i   = [line i j | j <- [0..n-1]]
          line i j = if j == 0
                     then to : [from..from+i-1]
                     else [from+j*i-1..from+(j+1)*i-1]
              where from = n * i * (i - 1) `div` 2 + 1
                    to   = n * i * (i + 1) `div` 2

connectTriangles :: [[[Int]]] -> [(Int,Int,Int)]
connectTriangles [x]      = []
connectTriangles (x:y:xs) = connect x y ++ connectTriangles (y:xs)
    where connect x y  = concat $ zipWith connectLine x y
          connectLine [x]        [y1,y2]    = [(x,y2,y1)]
          connectLine (x1:x2:xs) (y1:y2:ys) = (x1,y2,y1):(y2,x1,x2):connectLine (x2:xs) (y2:ys)

affinComb :: Double -> Point -> Point -> Point
affinComb a p q = vplus p' q'
    where p' = vmul (1 - a) p
          q' = vmul a q

vplus :: Point -> Point -> Point
vplus a b = zipWith (+) a b

vmul :: Double -> Point -> Point
vmul x a = map (* x) a

eval :: Polygon -> [Index] -> [Point] -> Point -> Point
eval ps is cps p = foldr1 vplus [vmul (bernstein i us) cp | (cp,i) <- zip cps is]
    where us = barycentric ps p

{- Standard control point positions

(X,Y) coordinates of the control points are defined as combinations
of the domain polygon's vertices, e.g. [1,2,0,0,0] is the affine combination
of [3,0,0,0,0] and [0,3,0,0,0].

Then the points are raised onto a paraboloid.

-}

cp3D :: Int -> Int -> [Point]
cp3D n d = map cp (indices n d) -- ((outerIndices n d) ++ (innerIndices n d))
    where ps     = regularPolygon n
          -- ps     = [[-1,1],[-1,-1],[1,-1],[1,-1/3],[-1/3,-1/3],[-1/3,1]]
          -- ps     = [[-1,1],[-1,-1],[1,-1],[1,-1/3],[-1/3,-1/3],[-1/3,1/3],[1,1/3],[1,1]]
          -- ps     = [[-1,1],[-1,-1],[1,-1],[1,-1/2],[-1/2,-1/2],[-1/2,1/2],[1,1/2],[1,1]]
          -- ps     = [[-1,1],[-1,-1],[0,-1],[0,0],[-2/3,0],[-2/3,2/3],[1,2/3],[1,1]]
          -- ps     = [[-1,7/8],[-1,-1],[1/8,-1],[0,-1/4],[-5/8,-3/8],[-1/2,1/2],[7/8,1/2],[3/4,1]]
          cp     = to3D . foldr1 vplus . wcp
          wcp xs = zipWith op (map fromIntegral xs) ps
          op a p = vmul (a / fromIntegral d) p
          to3D [x,y] = [x,y,0] --[x,y,1.0-x*x-y*y]

{- Alternative method

Given boundary vertices p_i, and inner boundary vertices q_i,
the coordinates of a control point c_j having index j = {j1,...,jn}
is defined as 1/d * sum j_i p_i + alpha / d * sum j_i (q_i - p_i),
where alpha = (1 - dist(j)) / (1 - dist(k)),
k being the index of an (arbitrary) inner boundary vertex,
and dist() is the distance of the domain position from the origin.

Note that this gives back the correct values for p_i and q_i.

-}

square :: Double -> Double
square x = x * x

norm2 :: [Double] -> Double
norm2 = foldr1 (+) . map square

isInnerCorner :: Index -> Bool
isInnerCorner xs = zeroes == n - 3 && pat1n1 xs'
    where n      = length xs
          zeroes = length $ filter (== 0) xs
          pat1n1 [_,_]     = False
          pat1n1 (1:_:1:_) = True
          pat1n1 (_:ys)    = pat1n1 ys
          xs'    = xs ++ xs

innerDistance :: Int -> Int -> Double
innerDistance n d = norm2 (init cp)
    where cp = snd $ head $ filter (isInnerCorner . fst) $ zip (indices n d) (cp3D n d)

distance :: Index -> Double
distance xs = norm2 (init cp)
    where cp = snd $ head $ filter ((== xs) . fst) $ zip (indices n d) (cp3D n d)
          n = length xs
          d = sum xs

deviationWeight :: Index -> Double
deviationWeight xs = (1.0 - distance xs) / (1.0 - innerDistance n d)
    where n = length xs
          d = sum xs

-- Tests

surf3D :: Int -> Int -> Int -> [Point]
surf3D n d res = map (eval ps is cp) xs
    where is = indices n d
          cp = cp3D n d
          ps = regularPolygon n
          xs = samplePoints ps res

cpVTK :: Int -> Int -> String
cpVTK n d = "# vtk DataFile Version 1.0\n\
            \S-Patch Control Net\n\
            \ASCII\n\
            \DATASET POLYDATA\n\
            \POINTS " ++ show (length cp) ++ " float\n" ++
            concat [showPoint p ++ "\n" | p <- cp] ++
            "LINES " ++ show (length lines) ++ " " ++ show (3 * length lines) ++ "\n" ++
            concat ["2 " ++ show a ++ " " ++ show b ++ "\n"| (a,b) <- lines]
    where cp    = cp3D n d
          is    = indices n d
          lines = controlNet is

controlNet :: [Index] -> [(Int, Int)]
controlNet is = filter (uncurry (<)) $ concat $ map op isid
    where op i  = [(pos j, snd i) | j <- neighbors (fst i), any (== j) is]
          pos i = snd $ head $ dropWhile ((/= i) . fst) isid
          isid  = zip is [0..]

showPoint :: Point -> String
showPoint = intercalate " " . map show

cpSKD :: Int -> Int -> String
cpSKD n d = "; Sketches Data File\n\
            \; Do not edit this file!\n\
            \[VERSION]\n\
            \44\n\
            \[PARAMETERS]\n\
            \[FREE_CLUBS]\n" ++ show (length cp) ++ "\n" ++
            concat [show x ++ " " ++ showPoint (scaled p) ++ " 0 -1 0\n"
                        | (x,p) <- zip [0..] cp] ++
            "[MAGNETIC_CLUBS]\n0\n\
            \[CURVES]\n" ++ show (length lines) ++ "\n" ++
            concat [show x ++ " 0 0 0 0 -1 0 2 " ++ show a ++ " " ++ show b ++ "\n"
                        | (x,(a,b)) <- zip [length cp..] lines] ++
            "[SURFACES]\n0\n\
            \[AUXILIARY_CLUBS]\n0\n\
            \[INTERPOLATED_CLUBS]\n0\n\
            \[AUXILIARY_CURVES]\n0\n\
            \[SURFACE_CLUBS]\n0\n\
            \[TRIM_CURVES]\n0\n\
            \[PLANES]\n0\n\
            \[SKETCHBOX]\n\
            \SKETCHBOX_SIZES=100x100x100\n\
            \SKETCHBOX_CENTER=0x0x0\n\
            \GRID=1,5,1\n\
            \[VIEWS]\n0\n\
            \[COMPOSITION]\n\n\
            \[MESHES]\n0\n\
            \[SPECTRUM]\n0\n0\n\
            \[TEXTURE]\n0\n\
            \[HISTORY]\n0 0\n\
            \[END]\n"
    where cp    = cp3D n d
          -- is    = (indices n d)
          is    = (outerIndices n d) ++ (innerIndices n d)
          lines = controlNet is
          scaled = map (100.0 *)

showLine :: [Point] -> (Int, Int) -> String
showLine cp (from, to) = "newpath\n" ++
                         (showScaled from) ++ " moveto\n" ++
                         (showScaled to) ++ " lineto\n" ++
                         "stroke\n"
    where showScaled = showPoint . scale . (cp !!)
          scale      = map (\x -> x * 250.0 + 300.0)

cpEPS :: Int -> Int -> String
cpEPS n d = "%!PS-Adobe-2.0\n\
            \%%BoundingBox: 0 0 600 600\n" ++
            (concat $ map (showLine cp) lines) ++
            concat [showPoint (scale p) ++ " 3 0 360 arc fill\n" | p <- cp] ++
            "showpage\n"
    where cp    = map init $ cp3D n d
          is    = (indices n d)
          -- is    = (outerIndices n d) ++ (innerIndices n d)
          lines = controlNet is
          scale = map (\x -> x * 250.0 + 300.0)

surfVTK :: Int -> Int -> Int -> String
surfVTK n d res = "# vtk DataFile Version 1.0\n\
                  \S-Patch Surface\n\
                  \ASCII\n\
                  \DATASET POLYDATA\n\
                  \POINTS " ++ show (length ps) ++ " float\n" ++
                  concat [showPoint p ++ "\n" | p <- ps] ++
                  "POLYGONS " ++ show (length ts) ++ " " ++ show (4 * length ts) ++ "\n" ++
                  concat ["3 " ++ showTriangle t ++ "\n" | t <- ts]
    where ps = surf3D n d res
          ts = triangles n res

showTriangle :: (Int, Int, Int) -> String
showTriangle (a,b,c) = show a ++ " " ++ show b ++ " " ++ show c

-- >>> writeFile "/tmp/5sided-cubic-net.vtk" $ cpVTK 5 3
-- >>> writeFile "/tmp/5sided-cubic.vtk" $ surfVTK 5 3 50

writeEPS = mapM_ out [(n,d) | n <- [8], d <- [1..5]]
    where out (n,d) = writeFile (fname n d) (cpEPS n d)
          fname n d = "/tmp/spatch-" ++ show n ++ "-" ++ show d ++ ".eps"

main = mapM_ out [(n,d) | n <- [3..8], d <- [1..5]]
    where out (n,d) = writeFile (fname n d) (cpSKD n d)
          fname n d = "/tmp/spatch-" ++ show n ++ "-" ++ show d ++ ".skd"
