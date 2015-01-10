
-- import Prelude()
-- import Prelude (Show (..), Read (..), Eq (..), String, Integer,
                 -- map, (++), Maybe (..), ($), fst, not, elem, 
                 -- notElem, reads, Char)
import Prelude hiding ((.), id, iterate, foldl)
import Control.Monad(liftM2, (>=>), (>>=), fmap, mplus)
import Control.Category(Category (id, (.)))

import Iso
import TH


-- :set -XTemplateHaskell


-- Te warninge vrača
-- Isomorphismi.hs:85:9: Warning:
    -- Local definition of ‘<*>’ clashes with a future Prelude name - this will become an error in GHC 7.10, under the Applicative-Monad Proposal.

-- Isomorphismi.hs:98:9: Warning:
    -- Local definition of ‘pure’ clashes with a future Prelude name - this will become an error in GHC 7.10, under the Applicative-Monad Proposal.

-- infixl 3 <|> 
-- infixr 6 <*>
-- infixl 4 <+>


data List a = Nil
            | Cons a (List a)
			

data Iso a b = Iso (a -> Maybe b) (b -> Maybe a)

inverse :: Iso a b -> Iso b a
inverse (Iso f g) = Iso g f

apply :: Iso a b -> a -> Maybe b
apply (Iso f g) = f

unapply :: Iso a b -> b -> Maybe a
unapply = apply . inverse




nil :: Iso () (List a)
cons :: Iso (a, List a) (List a)

nil = Iso (\ () -> Just Nil)
			(\ xs -> case xs of
						Nil -> Just ()
						Cons x xs -> Nothing)

cons = Iso (\ (x,xs) -> Just (Cons x xs))
			(\ xs -> case xs of
						Nil -> Nothing
						Cons x xs -> Just (x,xs))

-- nil :: Iso () ([a])
-- cons :: Iso (a, [a]) ([a])

-- nil = Iso (\ () -> Just [])
			-- (\ xs -> case xs of
						-- [] -> Just ()
						-- (x:xs) -> Nothing)

-- cons = Iso (\ (x, xs) -> Just (x:xs))
			-- (\ xs -> case xs of
						-- [] -> Nothing
						-- (x:xs) -> Just (x,xs))


instance Category Iso where
	g . f = Iso (apply f >=> apply g) (unapply g >=> unapply f)
	id = Iso Just Just


	
	
constructorIso c = do
  DataConI n _ d _             <-  reify c
  TyConI ((DataD _ _ _ cs _))  <-  reify d
  let Just con = find (\(NormalC n' _) -> n == n') cs
  isoFromCon con

defineIsomorphisms d = do
  TyConI (DataD _ _ _ cs _) <- reify d
  let rename n 
        = mkName (toLower c : cs) where c : cs = nameBase n
      defFromCon con@(NormalC n _) 
        =  funD (rename n) 
             [clause [] (normalB (isoFromCon con)) []]  
  mapM defFromCon cs

isoFromCon (NormalC c fs) = do
  let n     =   length fs
  (ps, vs)  <-  genPE n
  v         <-  newName "x"
  let f     =   lamE [nested tupP ps] [| Just $(foldl appE (conE c) vs) |]
  let g     =   lamE [varP v] 
                  (caseE (varE v) 
                    [ match (conP c ps) 
                        (normalB [| Just $(nested tupE vs) |]) [] 
                    , match (wildP) 
                        (normalB [| Nothing |]) []])
  [| Iso $f $g |]

genPE n = do
  ids <- replicateM n (newName "x")
  return (map varP ids, map varE ids)

nested tup []      =  tup [] 
nested tup [x]     =  x
nested tup (x:xs)  =  tup [x, nested tup xs]


class IsoFunctor f where
	(<$>) :: Iso a b -> (f a -> f b)
	
-- to kao ni dobro, ka implicira na un Iso in je spodnja verzija bulša, 
-- ka je bol splošna
-- class IsoApplicative f where
	-- (<*>) :: f (Iso a b) -> (f a -> f b)
	
class ProductFunctor f where
	(<*>) :: f a -> f b -> f(a, b)
	
class Alternative f where
	(<|>) :: f a -> f a -> f a
	empty ::  f a


class (IsoFunctor d, ProductFunctor d, Alternative d) 
	=> Syntax d where
	-- (<$>)::Iso a b -> d a -> d b
	-- (<*>):: d a -> d b -> d(a,b)
	-- (<|>):: d a -> d a -> d a
	-- empty:: d a
	pure :: Eq a => a -> d a
	token:: d Char
	

	
-- to mi ne dela ???
-- many :: Syntax d => d a -> d [a]
-- many p = nil <$> pure() <|> cons <$> p <*> many p


newtype Parser a = Parser (String -> [(a, String)])

parse::Parser a -> String -> [a]
parse (Parser p) s = [x | (x, "") <- p s]

instance IsoFunctor Parser where
	iso <$> Parser p = Parser(\ s -> [(y,s') | (x,s') <- p s, Just y <- [apply iso x]])

instance ProductFunctor Parser where
	Parser p <*> Parser q = Parser (\ s -> [((x,y),s'')|(x,s) <- p s, (y,s'') <-q s])

instance Alternative Parser where
	Parser p <|> Parser q = Parser (\ s -> p s ++ q s)
	empty = Parser (\ s -> [])

instance Syntax Parser where
	pure x = Parser (\ s -> [(x,s)])
	token = Parser f where
			f [] = []
			f (t:ts) = [(t,ts)]
			

			
newtype Printer a = Printer (a -> Maybe String)

print:: Printer a -> a -> Maybe String
print (Printer p) x = p x

instance IsoFunctor Printer where
	iso <$> Printer p = Printer (\ b -> (unapply iso b) >>= p)
	
instance ProductFunctor Printer where
	Printer p <*> Printer q = Printer (\ (x,y) -> liftM2 (++) (p x) (q y))

instance Alternative Printer where
	-- (p s) če to ne uspe pa (q s)
	Printer p <|> Printer q = Printer (\ s -> mplus (p s) (q s))
	empty = Printer (\s -> Nothing)
	
instance Syntax Printer where
	pure x = Printer (\y -> if x == y then Just "" else Nothing)
	token = Printer (\t -> Just[t])
	

	
data Rel a = Rel[(a,String)]

-- kaj dela return? a ne smo vrne just neki, ampak to nrdi že f od isota...
-- return ni tuki
instance IsoFunctor Rel where
	Iso f g <$> Rel graph = Rel [(a',c) | (a,c) <- graph, Just a' <- return (f a)]
	
instance ProductFunctor Rel where
	Rel graph <*> Rel graph' = Rel [((a,a'), c++c') |(a,c)<- graph, (a',c') <-graph']
	
instance Alternative Rel where
	Rel graph <|> Rel graph' = Rel (graph ++ graph')
	empty = Rel[]
	
instance Syntax Rel where
	pure x = Rel[(x,"")]
	token = Rel[(t,[t])| t<-characters] where characters=[minBound..maxBound]
	
	
(***)::Iso a b -> Iso c d -> Iso (a,c) (b,d)
i *** j = Iso f g where
	f (a,c) = liftM2(,) (apply i a) (apply j c)
	g (b,d) = liftM2(,) (unapply i b) (unapply j d)
	
associate::Iso (a,(b,c)) ((a,b),c)
associate = Iso f g where
	f(a,(b,c)) = Just ((a,b),c)
	g((a,b),c) = Just (a,(b,c))
	
commute = Iso f f where
	f(a,b) = Just (b,a)
	
unit = Iso f g where
	f a = Just (a,())
	g (a,()) = Just a
	
element:: Eq a => a -> Iso () a
element x = Iso (\a -> Just x) (\b -> if x == b then Just() else Nothing)
	
subset::(a -> Bool) -> Iso a a
subset p = Iso f f where
	f x | p x = Just x | otherwise = Nothing
	
-- foldl f (z, []) = z
-- foldl f (z, x:xs) = foldl f (f (z, x), xs)
	
driver step state = case step state of 
						Just state' -> driver step state'
						Nothing -> state

-- fst smo fn, ki vrne prvi elem tupla
-- foldl f = fst . driver step where
	-- step(z,[])=Nothing
	-- step(z,x:xs)=Just(f(z,x),xs)
	
-- step je tuki nek Iso, v def driverja je pa funkcija 
iterate step = Iso f g where
	f = Just . driver (apply step)
	g = Just . driver (unapply step)
	
step i = (i *** id) . associate . (id *** inverse cons)

foldl i = inverse unit . (id *** inverse nil) . iterate(step i)



-- Template haskell naredi da lhko pole uporablaš left right! poštudiri in napiši sam!!
-- $(defineIsomorphisms 00Either)

-- (<+>)::Syntax d => d a -> d b -> d (Either a b)
-- p <+> q = (left <$> p) <|> (right <$> q)

-- listCases:: Iso (Either () (a,[a])) [a]
-- listCases = Iso f g where
	-- f (Left()) = Just []
	-- f (Right(x,xs)) = Just (x:xs)
	-- g [] = Just (Left())
	-- g (x:xs) = Just (Right(x,xs))
	
-- text:: Sytnax d => String -> d ()
-- text [] = pure()
-- text (c:cs) = inverse(element((),())) <$> (inverse (element c) <$> token) <*> text cs

-- many p = listCases <$> (text "" <+> p <*> many p)









































-- kvadrat = Iso (\(a) -> Just (a^2)) (\b -> Just (sqrt b))


-- brisi "" = ""
-- brisi (t:xt) = if t == ' ' then (brisi xt) else t:xt
-- presledki = Iso (\txt -> Just (brisi txt)) (\txt -> Just (" " ++ txt))

-- ignore :: a -> Iso a ()
-- ignore x = Iso f g where
	-- f _ = Just ()
	-- g () = Just x

-- ignore3 = ignore 3




-- razdelek2 odpri zapri count del (t:xt) = 
	-- if t == odpri
	-- then razdelek2 odpri zapri (count+1) (t:del) xt
	-- else if t == zapri
		-- then if count == 0 then [reverse del, xt] else razdelek2 odpri zapri (count-1) (t:del) xt
		-- else razdelek2 odpri zapri count (t:del) xt

		
-- razdelek3 odpri zapri count del [] = [reverse del, ""]
-- razdelek3 odpri zapri count del (t:xt) = 
	-- if t == odpri
	-- then razdelek3 odpri zapri (count+1) (t:del) xt
	-- else 
		-- if t == zapri
		-- then 
			-- if count == 0 
			-- then [reverse del, xt] 
			-- else razdelek3 odpri zapri (count-1) (t:del) xt
		-- else razdelek3 odpri zapri count (t:del) xt

-- razdelek '(' ')' 0 "ndlaskn(dsalk)dsam\nnkl(dksal((dsalk)ds))dsnkla)dnsalkdnsa12334"
-- razdelek2 '(' ')' 0 "" "ndlaskn(dsalk)dsam\nnkl(dksal((dsalk)ds))dsnkla)dnsalkdnsa12334"

-- let pat = "(foo[a-z]*bar|quux)"
-- "before foodiebar after" =~ pat :: (String,String,String)

-- parse_funkcija2 text = [ime, arg, telo]
	-- where
	-- (_,_, ostanek) = text =~ "(def )" :: (String,String,String)
	-- (ime,_, ostanek2) = ostanek =~ "[(]" :: (String,String,String)
	-- (arg,_, telo) = ostanek2 =~ "[)]" :: (String,String,String)


-- parse_funkcija text = [ime, arg, telo]
	-- where
	-- [ime, arg_telo] = razdelek2 ';' '(' 0 "" text
	-- [arg, telo] = razdelek2 '(' ')' 0 "" arg_telo
	
-- print_funkcija [ime, arg, telo] = ime ++ "(" ++ arg ++ ")" ++ telo

-- py_fun = "ime_funkcije(argumenti, argumenti, argumenti): telo"
-- py_fun2 = "def ime_funkcije(argumenti, argumenti, argumenti): telo"
-- parse_funkcija py_fun

-- funkcija = Iso (\(a) -> Just (parse_funkcija a)) (\b -> Just (print_funkcija b))





-- parse_while text = [pogoj, telo]
	-- where
	-- [pogoj, telo] = razdelek2 ';' ':' 0 "" text
	
-- print_while [pogoj, telo] = pogoj ++ telo

-- while = Iso (\(a) -> Just (parse_while a)) (\b -> Just (print_while b))


-- py_while = "spremenljivka < 10.4: spremenljivka+=1"
-- parse_while py_while
	
	
	


	
	
	