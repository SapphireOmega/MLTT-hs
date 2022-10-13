{-# LANGUAGE UnicodeSyntax #-}

import Text.Parsec
import Data.Function

type Identifier    = String
type Combination a = [a]
data Expression    = Constant Identifier
                   | Abstraction (Combination Identifier) Expression
                   | Application Expression (Combination Expression)
                   deriving (Show)
data Arity         = Zero
                   | Unknown Identifier
                   | Arrow Arity Arity
                   | Product [Arity]
                   deriving (Show)
type Namespace     = [(Identifier, Arity)]
type TTParser a    = Namespace → Parsec String () (a, Arity)

(≡) ∷ Eq a => a -> a -> Bool
(≡) = (==)

(∈) ∷ (Foldable t, Eq a) => a -> t a -> Bool
(∈) = elem

--(.:) :: (c → d) → (a → b → c) → a → b → d
--(.:) = (.) . (.)

warbler ∷ (a → a → b) → a → b
warbler f x = f x x

namespaceLookup ∷ Namespace → Identifier → Arity
namespaceLookup namespace iden =
  case lookup iden namespace of
    Just x  → x
    Nothing → Unknown iden

(*><) ∷ Applicative f => f a -> f b -> f b
(*><) = warbler (*><*)

(*><*) ∷ Applicative f => f a -> f b → f c -> f c
p1 *><* p2 = \parser → p1 *> parser <* p2

parenned ∷ Parsec String a b → Parsec String a b
parenned parser = (spaces *>< char '(') *> parser <* (spaces *>< char ')')
--parenned parser = ((parser &) .: (*><*) `on` (spaces *><) . char) '(' ')'

identifier ∷ TTParser Identifier
identifier namespace = addNoiseHandling $ applyLookup $ core
  where
    core = many1 $ noneOf "(), "
    addNoiseHandling parser = spaces *>< (parenned (identifier namespace) <|> parser)
    applyLookup = ((\iden → (iden, namespaceLookup namespace iden)) <$>)

-- Arity will always a Product, even when there is just 1 element in
-- the combination. This may be odd, but it makes the code simpler.
combination ∷ TTParser a → TTParser (Combination a)
combination parser namespace = applyLookup $ spaces *>< (parenned $ parser namespace `sepBy1` (spaces *>< char ','))
  where
    applyLookup = ((\x → let (exprs, arities) = unzip x in (exprs, Product arities)) <$>)

abstraction ∷ TTParser Expression
abstraction namespace = try (parenned $ abstraction namespace) <|> do
  -- We will be ingoring the arities of the args, since they should
  -- all be unknown rather than be bound to the surrounding namespace.
  (idens, _)        ← combination identifier namespace
  (expr, exprArity) ← expression namespace
  return (Abstraction idens expr, Arrow (Product $ map (\x → Unknown x) idens) exprArity)

-- This should be run inside out during parsing, so the namespaces
-- stay correct.
substituteArity ∷ Namespace → Arity → Arity
substituteArity namespace = core 
  where
    core ∷ Arity → Arity
    core Zero           = Zero
    core (Unknown iden) = namespaceLookup namespace iden
    core (Arrow x y)    = Arrow (core x) (core y)
    core (Product xs)   = Product (map core xs)

application ∷ TTParser Expression
application namespace = try (parenned $ application namespace) <|> do
  (expr, exprArity)          ←  try ((\(iden, arity) → (Constant iden, arity)) <$> identifier namespace)
                            <|> try (abstraction namespace)
                            <|> parenned (expression namespace)
  (args, argsArity)          ←  combination expression namespace
  let (unknowns, bodyArity)  = splitArrow exprArity
  let localNamespace         = createNamespace unknowns (aritiesFromProduct argsArity)
  return (Application expr args, substituteArity localNamespace bodyArity)
  where
    aritiesFromProduct ∷ Arity → [Arity]
    aritiesFromProduct (Product xs) = xs
    aritiesFromProduct _ = error "In application parser: arg combination has unexpected arity (Product expected)"
    splitArrow ∷ Arity → ([Arity], Arity)
    splitArrow (Arrow (Product unknowns) body) = (unknowns, body)
    splitArrow _ = error "In application parser: applied expression not of arity arrow or hole(s) don't form a product"
    getIden ∷ Arity → Identifier
    getIden (Unknown iden) = iden
    getIden _ = error "idensFromUnknowns encountered arity other than unknown"
    createNamespace ∷ [Arity] → [Arity] → Namespace
    createNamespace unknowns arities = zip (map getIden unknowns) arities

expression ∷ TTParser Expression
expression namespace  =  try (application namespace)
                     <|> try (abstraction namespace)
                     <|> ((\(x,y) → (Constant x, y)) <$> (identifier namespace))

normalize ∷ Expression → Expression
normalize (Application func args) =
  case func of (Application _ _)      → normalize (Application (normalize func) args)
               (Abstraction ids body) → substituteAll ids args body
               _                      → (Application func args)
normalize x = x

substituteAll ∷ Combination Identifier → Combination Expression → Expression → Expression
substituteAll ids args expr = foldl (&) expr $ map substitute $ zip ids args

substitute ∷ (Identifier, Expression) → Expression → Expression
substitute (argname, arg) = \expr →
  case expr of (Constant ident)        → if argname ≡ ident
                                           then arg
                                           else (Constant ident)
               (Abstraction ids body)  → if argname ∈ ids
                                           then (Abstraction ids body)
                                           else (Abstraction ids (repeatFor body))
               (Application func args) → Application (repeatFor func) (map repeatFor args)
  where repeatFor = substitute (argname, arg)
                 
parseTT ∷ Namespace → String → Either ParseError (Expression, Arity)
parseTT namespace = parse (expression namespace <* eof) ""

source ∷ String
source = "((x,y)+(y,x))(1,2)"

testNamespace ∷ Namespace
testNamespace = [ ("+", Arrow (Product [Zero,Zero]) Zero)
                , ("1", Zero)
                , ("2", Zero)
                ]

program ∷ Either ParseError (Expression, Arity)
program = parseTT testNamespace source

normalProgram ∷ Either ParseError Expression
normalProgram = (normalize . fst) <$> program

main ∷ IO ()
main = do
  putStrLn "Parsed program:"
  putStrLn $ show program
  putStrLn "Evaluated program:"
  putStrLn $ show normalProgram
