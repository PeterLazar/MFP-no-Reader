module C where

-- to je treba upisat u ghci, čene template haskell ne dela
-- :set -XTemplateHaskell

import Prelude hiding ((.), id, print)

import Control.Monad.Reader

import Control.Category

import Data.Char (isLetter, isDigit)
import qualified Data.Text
import Unparse
import Iso
import TH

data Config = Config {
		brackets::Bool,
		ifNewLine::Bool
    }


data Expression = Variable String
				| Literal Integer
				| BinOp Expression Operator Expression
				| IfExp Expression Expression
				deriving (Show, Eq)
				
data Operator = AddOp
				| MulOp
				| DivOp
				| SubOp
				| EqOp
				deriving(Show, Eq)
	

$(defineIsomorphisms ''Expression)
$(defineIsomorphisms ''Operator)


keywords = ["else","for","while","True","False","global","switch","case","return"]

letter, digit:: Syntax d => d Char
letter = subset isLetter <$> token
digit = subset isDigit <$> token


identifier :: Syntax f => f [Char]
identifier = subset (`notElem` keywords) . cons <$> letter <*> many (letter <|> digit)


keyword::Syntax d => String -> d ()
keyword s = inverse right <$> (identifier <+> text s)


ops :: Syntax f => f Operator
ops = mulOp <$> text "*" 
	<|> addOp <$> text "+" 
	<|> divOp <$> text "/" 
	<|> subOp <$> text "-"
	<|> eqOp <$> text "=="


ignore:: a -> Iso a ()
ignore x = Iso f g where
			f _ = Just ()
			g () = Just x

skipSpace, optSpace, sepSpace::Syntax d => d()
skipSpace = ignore [] <$> many(text " " <|> text "\n")
optSpace = ignore [()] <$> many(text " " <|> text "\n")
sepSpace = text " " <|> text "\n" <* skipSpace
-- lineSpace = text "\n" <* skipSpace

integer::Syntax d => d Integer
integer = Iso read' show' <$> many digit where
	read' s = case[x|(x,"")<-reads s] of
				[] -> Nothing
				(x:_) -> Just x
	show' x = Just(show x)

parens :: Syntax d => d a -> d a
parens = between (text "(" <* skipSpace) (skipSpace *> text ")")


curly_parens :: Syntax d => d a -> d a
curly_parens = between (text "{" <* skipSpace) (skipSpace *> text "}")


spacedOps :: Syntax d => d Operator
spacedOps = between optSpace optSpace ops

priority:: Operator -> Integer
priority MulOp = 1
priority DivOp = 1
priority SubOp = 2
priority AddOp = 2
priority EqOp = 3


expression:: Syntax d => Config -> d Expression
expression conf = exp 3 where
	exp 0 = literal <$> integer
			<|> variable <$> identifier
			<|> ifExp <$> ifExp_fn
			<|> parens (skipSpace *> (expression conf) <* skipSpace)

	exp 1 = chainl1 (exp 0) spacedOps (binOpPrio 1)
	exp 2 = chainl1 (exp 1) spacedOps (binOpPrio 2)
	exp 3 = chainl1 (exp 2) spacedOps (binOpPrio 3)
		
	binOpPrio n = binOp . subset (\ (x,(op,y)) -> priority op == n)
	
	
	-- printer/parser if stavka z zavitimi oklepaji
	ifExp_bracket :: Syntax d => d (Expression, Expression)
	ifExp_bracket = keyword "if"
		*> optSpace *> parens (expression conf)
		-- <*> (optSpace *> expression) --curly_parens (expression)
		<*> optSpace *> curly_parens (expression conf)

	-- printer/parser if stavka brez zavitih oklepajev
	ifExp_free :: Syntax d => d (Expression, Expression)
	ifExp_free = keyword "if"
		*> optSpace *> parens (expression conf)
		<*>  sepSpace *> (expression conf)

	-- printanje/parsanje if stavka implementiramo kot alternativo br <|> no_br
	-- za parsanje vrstni red ni pomemben
	-- za printanje pa je, saj je rezultat skupnega printerja kar rezultat prvega
	-- izmed alternativ, ki uspe
	-- če želimo printati if z zavitimi oklepaji, bomo morali napisati br <|> no_br
	-- če želimo printati brez pa no_br <|> br
	ifExp_fn :: Syntax d => d (Expression, Expression)
	ifExp_fn = (if b then (ifExp_bracket <|> ifExp_free) else (ifExp_free <|> ifExp_bracket))
		where Config {brackets=b} = conf
	



default_cfg = Config { brackets = True, ifNewLine = True}
cfg2 = Config {brackets = False, ifNewLine = True}

-- a = parse expression "a+4; if (a0== 0)\n {3}"


-- Examples
b = parse (expression default_cfg) "a+(b+3)/4*5 == 3"
c = parse (expression default_cfg) "if (2+3*4) 5"
d = parse (expression default_cfg) "{a+(b+3)/4*5 == 3; a+b;}"

x1 = "if (2+3*4) 5"
x2 = "if (2+3*4) {5+4}"

pp x = print (expression default_cfg) (head (parse (expression default_cfg) x))
pp2 x = print (expression cfg2) (head (parse (expression cfg2) x))

e = pp x1
f = pp2 x2




